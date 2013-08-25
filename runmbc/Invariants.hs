module Invariants where

import qualified Data.Map as M
import Data.Maybe
import Control.Monad.Error
import Control.Applicative
import Language.Eiffel.Syntax
import Language.Eiffel.Util
import Language.Eiffel.Position
import Util

-- | Modify cls to false positives in class invariant checking due to
-- | 1) callbacks
-- | 2) invariants that depend on other oobjects' fields
processInvariants :: [Clas] -> Clas -> ErrorT String IO Clas
processInvariants classes cls = foldM (flip ($)) cls 
  [
    addOpenAttribute classes, 
    guardInvariants,
--    guardPostconditionsAll,
    generateExtraInvariants classes,
    addOpenRestoreAll classes
  ]
  
openName = "open_"

setOpenName = "set_" ++ openName

-- | Add the "open" attribute and a setter for it to cls
addOpenAttribute classes cls = return cls { 
  featureClauses = featureClauses cls ++ 
    [FeatureClause { exportNames = map className classes
                  , attributes = [openAttr]
                  , routines = [setOpenProc]
                  , constants = []
                  }],
  inherit = map (\i -> i { inheritClauses = (map redefineOpen) (inheritClauses i)}) (inherit cls)
  }
  where
    openAttr = Attribute { attrFroz = False
            , attrDecl = Decl openName boolType
            , attrAssign = Nothing
            , attrNotes = [specNote]
            , attrReq = Contract True []
            , attrEns = Contract True []
            }
    argName = "b"
    setOpenProc =  AbsRoutine { routineFroz = False
            , routineName = setOpenName
            , routineAlias = Nothing
            , routineArgs = [Decl argName boolType]
            , routineResult = NoType
            , routineAssigner = Nothing
            , routineNote = [specNote]
            , routineProcs = []
            , routineReq = Contract True []
            , routineReqLk = []
            , routineImpl = RoutineBody [] [] (assign (var openName) (var argName))
            , routineEns = Contract True []
            , routineEnsLk = []
            , routineRescue = Nothing
            }
    redefineOpen ic = case classOfType classes cls (inheritClass ic) of
      Nothing -> ic
      _ -> ic { redefine = redefine ic ++ [openName, setOpenName] }

-- | Add opening and restoring instructions to all routines in cls
addOpenRestoreAll classes cls = classMapRoutinesM (addOpenRestore classes cls) cls
            
-- | Add opening and restoring instructions to routine
addOpenRestore classes cls routine = if not (isSpecOnly routine)
  then case routineImpl routine of
    RoutineBody locals procs body -> do
      mapM_ checkOpenName explicitOpens
      return $ routine {
        routineImpl = RoutineBody (newLocals locals) procs (newBody body)
      , routineRescue = newRescue (routineRescue routine) 
      }
    _ -> return routine
  else return routine  
  where
    explicitOpens = noteValues openClause (routineNote routine)
    allOpens = if not (isPrivateRoutine cls routine) && not (isCreate cls routine)
        then currentVar : (map var explicitOpens)
        else map var explicitOpens
    checkOpenName s = case M.lookup s (argMap routine) of
      Nothing -> throwError ("open clause of feature " ++ routineName routine ++ " lists a name that is not an argument: " ++ s)
      Just t -> case classOfType classes cls t of
        Nothing -> throwError ("The type " ++ show t ++ " of the argument " ++ s ++ " listed in the open clause of feature " ++ routineName routine ++ " is not based on a class under processing")
        _ -> return ()
    newLocals locals = locals ++ map (\arg -> Decl (localName arg) boolType) allOpens
    newBody stmt = block (
      map saveLocal allOpens ++
      map setOpen allOpens ++
      [stmt] ++
      map restore allOpens)
    newRescue resc = if null (allOpens)
      then resc
      else case resc of 
        Nothing -> Just $ map restore allOpens
        Just stmts -> Just $ stmts ++ (map restore allOpens)
    localName arg = case contents arg of
      CurrentVar -> "old_open_"
      VarOrCall a -> "old_" ++ a ++ "_open_"
    saveLocal arg = assign (var $ localName arg) (call arg openName [])
    setOpen arg = callStmt (call arg setOpenName [litBool True])
    restore arg = callStmt (call arg setOpenName [(var $ localName arg)])
    
-- | Guard class invariants of cls with "not open implies ..."
guardInvariants cls = return cls { invnts = map guardClause (invnts cls) }

-- | Guard assertion clause c
guardClause c = c { clauseExpr = guarded (clauseExpr c) }
  where
    guarded e = (notExpr $ var openName) `implies` e
    
-- | Guard postconditions of all routines with "not open implies ..."    
guardPostconditionsAll cls = classMapRoutinesM (guardPostconditions cls) cls

-- | Guard postconditions of routine
guardPostconditions cls routine = if (isPublicRoutine cls routine || isPublicCreate cls routine) && not (isSpecOnly routine)
  then return routine { routineEns = (routineEns routine) { contractClauses = map guardClause (contractClauses (routineEns routine)) } }
  else return routine

-- | Generate invariants out of all special invariant routines    
generateExtraInvariants classes cls = do
  newInvs <- catMaybes <$> mapM (extraInvariant classes cls) (allRoutines cls)
  return cls { invnts = invnts cls ++ newInvs }

-- | Generate an invariant out of routine
extraInvariant classes cls routine = if not (invariantStatus `elem` noteValues statusClause (routineNote routine))
  then return Nothing
  else if not (null (routineArgs routine) && (routineResult routine == boolType))
    then throwError ("Routine " ++ r ++ " cannot be an invariant routine because it has arguments or does not return BOOLEAN")
    else do
      mapM_ checkDependName explicitDepends
      return $ Just (Clause { 
          clauseName = Just r
        , clauseExpr = if null explicitDepends 
            then notOpen `implies` unqualCall r []
            else (notVoid `andThen` notOpen) `implies` unqualCall r []
        })
  where
    r = routineName routine
    explicitDepends = noteValues dependClause (routineNote routine)
    allDepends = currentVar : (map var explicitDepends)
    checkDependName s = case typeByName classes cls s of
      Nothing -> throwError ("Name " ++ s ++ " in the dependency clause of the invariant function " ++ r ++ " does not denote a query of the enclosing class")
      Just t -> case classOfType classes cls t of
        Nothing -> throwError ("The type " ++ show t ++ " of the query " ++ s ++ " listed in the dependency clause of feature " ++ r ++ " is not based on a class under processing")
        _ -> return ()
    notVoid = foldl1 andExpr (map (\v -> notEqual (var v) litVoid) explicitDepends)
    notOpen = foldl1 andExpr (map (\arg -> notExpr (call arg openName [])) allDepends)
    