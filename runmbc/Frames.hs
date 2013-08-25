module Frames (addFrames) where

import Data.List
import Data.Maybe
import Data.Map ((!))
import qualified Data.ByteString.Char8 as BS
import Control.Monad.Error
import Control.Applicative
import Language.Eiffel.Syntax
import Language.Eiffel.Util
import Language.Eiffel.PrettyPrint
import Language.Eiffel.Position
import Util

-- | Adds frame postconditions to all public routines in cls, in a system composed of classes.
-- | classes only have to include suppliers and ancestor of cls that have models.
-- | Frame postconditions are inferred from 'modify' clauses of routines.
addFrames classes cls = if null unknown
  then classMapRoutinesM (addFramePostcondition classes cls) cls
  else throwError ("Model clause of class " ++ className cls ++ " lists unknown identifiers: " ++ concat (intersperse ", " unknown))
  where
     unknown = modelQueries cls \\ allFeatureNames classes cls

{- Modify specifications -}    

-- | Modify specification of a routine: list or (argument position, model query name) pairs
type ModifySpec = [(Int, String)]

-- | All values associated with k in l
lookupMany k l = [v | (k', v) <- l, k' == k]    

-- | Is argument arg of routine the target of the call or has type "like Current"?
isLikeCurrent arg routine = arg == 0 || case declType (routineArgs routine !! (arg - 1)) of
  Like "Current" -> True
  _ -> False
    
-- | An entry in a modify spec adapted along an inheritance chain cs:
-- | if i is a covariant argument, rename m accordingly.
-- | NOTE: only covariant arguments of type like Current are supported.
renameModel cs r (i, m) = if isLikeCurrent i r then (i, renamedMany cs m) else (i, m)    

-- | Modify specification of routine in class cls in a system composed of classes.
-- | If routine does not have a modify clause, modify specs are collected from immediate previous versions.
modifySpec :: [Clas] -> Clas -> Routine -> ModifySpec
modifySpec classes cls routine = nub (concatMap modifiesInVersion (latestVersions classes cls (routineName routine)) ++ creationModifies)
  where
    modifiesInVersion (cs, r) = case noteValues modifyClause (routineNote r) of
        [] -> concatMap (collectFromParent cs r) (parentVersions classes (last cs) (routineName r))
        ["nothing__"] -> []
        xs -> map ((renameModel cs r) . (stripArg r)) xs    
    stripArg r m = case BS.breakSubstring (BS.pack "__") (BS.pack m) of
      (xs, ys) | BS.null ys -> (0, m)
      (xs, ys) -> case elemIndex (BS.unpack xs) (map declName (routineArgs r)) of
        Nothing -> (0, m)
        Just k -> (k + 1, (BS.unpack (BS.drop 2 ys)))
    collectFromParent cs r (cs', r') = map (renameModel cs r . renameModel cs' r') (modifySpec classes (last cs') r')
    creationModifies = if isPublicCreate cls routine
      then zip (repeat 0) (modelQueries cls) 
      else []

-- Add frame postconditions to routine in class cls in a system composed of classes
addFramePostcondition classes cls routine = 
  let classOfArg arg = case arg of
        0 -> Just cls
        n -> classOfType classes cls (declType (routineArgs routine !! (n - 1)))
      fullArgList = CurrentVar : map (VarOrCall . declName) (routineArgs routine)
      argsInSystem = [i | i <- [0..(length fullArgList - 1)], isJust (classOfArg i)]
      myModifies = modifySpec classes cls routine
      unknownFor arg = zip (repeat (fullArgList !! arg)) (lookupMany arg myModifies \\ modelQueries (fromJust (classOfArg arg)))
      unknown = concat (map unknownFor argsInSystem)
      unchanged arg = filter (isNewUnchanged arg) (modelQueries (fromJust (classOfArg arg)) \\ lookupMany arg myModifies)
      myParentVersions = parentVersions classes cls (routineName routine)
      parentHasModel model (cs, _) = unrenamedMany cs model `elem` modelQueries (last cs)
      isInParentModify arg model (cs, r) = (arg, model) `elem` map (renameModel cs r) (modifySpec classes (last cs) r)
      isNewUnchanged arg model =
        null myParentVersions || -- routine is not inherited
        (isLikeCurrent arg routine && not (any (parentHasModel model) myParentVersions)) || -- model is a new model query compared to parent versions of the routine
        -- ToDo: only takes into account new model queries for Current and like Current args, not for other covariant redefinitions
        all (isInParentModify arg model) myParentVersions -- model is in the modify clause for all parent versions
      mayBeAliased i j = case (classOfArg i, classOfArg j) of
        (Just c1, Just c2) -> (c1 `elem` ancestors classes c2) || (c2 `elem` ancestors classes c1)
        _ -> False
      aliases arg = [(fullArgList !! i, m) | (i, m) <- myModifies, mayBeAliased i arg, not (m `elem` lookupMany arg myModifies)]
      toStr (i, m) = show i ++ "_" ++ m ++ "_"
      newPosts arg = noChanges classes (fromJust (classOfArg arg)) (fullArgList !! arg) (unchanged arg) (nub (map fst (aliases arg))) (nub (map snd (aliases arg)))
  in if null unknown
  then if (isPublicRoutine cls routine || isPublicCreate cls routine) && not (isSpecOnly routine) 
    then return (routine {routineEns = (routineEns routine) {contractClauses = (contractClauses . routineEns) routine ++ concat (map newPosts argsInSystem)}})
    else return routine
  else throwError ("Modify clause of feature " ++ className cls ++ "." ++ routineName routine ++ " lists non model queries: " ++ 
    concat (intersperse ", " (map (show . expr . uncurry callExpression) unknown)))
          
{- Code generation -}

-- | Is t a mathematical model type?    
isMMLType t = case t of
  ClassType name _ -> "MML_" `isPrefixOf` name
  _ -> False
  
-- | Is t an agent type?   
isAgentType t = case t of
  ClassType name _ -> name `elem` ["ROUTINE", "FUNCTION", "PREDICATE", "PROCEDURE"]
  _ -> False
  
-- | Expression arg.mq = old arg.mq with an appropriate equality
unchangedExpression arg mq t = if isMMLType t
  then Just (m |=| old m)
  else if isAgentType t
    then Nothing
    else Just (m `referenceEqual` old m)
  where 
    m = callExpression arg mq
    (|=|) e1 e2 = attachEmptyPos $ BinOpExpr (SymbolOp "|=|") e1 e2

-- | Call of query q on target t
callExpression t q = call (attachEmptyPos t) q []
    
-- | List of postconditions "m = old m" for all m in arg.models inside class cls in a system composed of classes,
-- | where any of aliasArgs.aliasModels is possibly aliased with arg.aliasModels    
noChanges classes cls arg models aliasArgs aliasModels = catMaybes (map noChange models)
  where
    modelType model = case typeByName classes cls model of
      Just t -> t
      Nothing -> error ("Cannot find model query " ++ model ++ " in class " ++ className cls)
    tag arg model = case arg of
      CurrentVar -> model ++ "_unchanged"
      VarOrCall a -> a ++ "_" ++ model ++ "_unchanged"
    notAliased model = if model `elem` aliasModels
      then Just (foldl1 andExpr (map (notEqual (attachEmptyPos arg) . attachEmptyPos) aliasArgs))
      else Nothing
    notVoid = case arg of
      CurrentVar -> Nothing
      VarOrCall v -> Just (notEqual (var v) litVoid)
    noChange model = case unchangedExpression arg model (modelType model) of
      Nothing -> Nothing
      Just e -> Just (Clause (Just (tag arg model)) (case notAliased model of
        Nothing -> case notVoid of
          Nothing -> e
          Just nv -> nv `implies` e
        Just na -> case notVoid of
          Nothing -> na `implies` e
          Just nv -> andExpr nv na `implies` e))
