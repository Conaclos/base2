module Util where

import Data.List
import Data.Maybe
import Language.Eiffel.Syntax
import Language.Eiffel.Util
import Language.Eiffel.Position

{- Specification notation -}

{-- Note clause names --}

modelClause = "model"
statusClause = "status"
modifyClause = "modify"
openClause = "open"
dependClause = "dependency"

{-- Note clause values --}

ghostStatus = "specification"
invariantStatus = "invariant__"
emptyModify = "nothing__"

{- Eiffel utilities -}
  
-- | List of identifiers marked by tag among notes
noteValues tag notes = 
  let 
    tagged = filter ((== tag) . noteTag) notes
    isVar (VarOrCall s) = Just s
    isVar _ = Nothing
  in case tagged of
    (Note _ xs: _ ) -> catMaybes (map isVar xs)
    _ -> []
  
-- | Parents of cls among classes  
parents classes cls = filter (\c -> className c `elem` map classNameType (allInheritedTypes cls)) classes

-- | Ancestors (reflexive transitive closure of parents) of cls among classes
ancestors classes cls = cls : concatMap (ancestors classes) (parents classes cls)

-- | New name of f from par in heir cls
renamed par cls f = case renames of
  [] -> f
  [r] -> renameNew r
  where
    inhClause = head (filter (\i -> classNameType (inheritClass i) == className par) (allInherited cls))
    renames = filter (\r -> renameOrig r == f) (rename inhClause)

-- | New name of f from (last cs) following the inheritance chain cs
renamedMany :: [Clas] -> String -> String    
renamedMany cs f = renamedMany' (reverse cs) f
  where
    renamedMany' [c] f = f
    renamedMany' (p:c:cs) f = renamedMany' (c:cs) (renamed p c f)
    
-- | Old name of f from cls in parent par    
unrenamed par cls f = case renames of
  [] -> f
  [r] -> renameOrig r
  where
    inhClause = head (filter (\i -> classNameType (inheritClass i) == className par) (allInherited cls))
    renames = filter (\r -> renameNew r == f) (rename inhClause)

-- | Old name of f from (head cs) following the inheritance chain cs backwards   
unrenamedMany :: [Clas] -> String -> String    
unrenamedMany [c] f = f
unrenamedMany (c:p:ps) f = unrenamedMany (p:ps) (unrenamed p c f)

-- | List of names of all features in cls (including inherited from any of classes)
allFeatureNames classes cls = map routineName (allRoutines cls) ++ 
  map (declName . attrDecl) (allAttributes cls) ++ 
  map (declName . constDecl) (allConstants cls) ++
  concatMap inheritedNames (parents classes cls)
  where 
    inheritedNames parent = map (renamed parent cls) (allFeatureNames classes parent)
    
-- | Mame of routine rName from c in its parent p
-- | When Nothing, routine does not exist in parent for sure
-- | When Just n, routine might not exist, but if it does it is called n
nameInParent :: [Clas] -> Clas -> Clas -> String -> Maybe String
nameInParent classes c p rName = if unrenamed p c rName == rName && renamed p c rName /= rName
  then Nothing
  else Just (unrenamed p c rName) 

-- | Latest version(s) of routine rName in cls or its parent and the inheritance path to it
latestVersions :: [Clas] -> Clas -> String -> [([Clas], Routine)]
latestVersions classes cls rName = case findRoutine cls rName of
  Just r -> [([cls], r)]
  Nothing -> parentVersions classes cls rName

-- | Latest version(s) of rName in direct ancestors of cls (excluding cls)
parentVersions :: [Clas] -> Clas -> String -> [([Clas], Routine)]
parentVersions classes cls rName = nub (concatMap versionFrom (parents classes cls))
  where
    versionFrom p = case nameInParent classes cls p rName of
      Nothing -> []
      (Just s) -> map update (latestVersions classes p s)
    update (cs, r) = (cls:cs, r)
    
-- | Does export list exps represent public export?   
isPublic exps = null exps || exps == ["ANY"]

-- | Does export list exps represent private export?
isPrivate exps = exps == ["NONE"]

-- | Is r a public routine in class c?
isPublicRoutine c r = case [clause | clause <- featureClauses c, r `elem` routines clause] of
  [] -> False
  [clause] -> isPublic (exportNames clause)
  _ -> error "Routine in multiple feature clauses"
  
-- | Is r a private routine in class c?
isPrivateRoutine c r = case [clause | clause <- featureClauses c, r `elem` routines clause] of
  [] -> False
  [clause] -> isPrivate (exportNames clause)
  _ -> error "Routine in multiple feature clauses"  
  
-- | Is r a creation procedure in c?
isCreate c r = isCreateName (routineName r) c || (null (creates c) && (routineName r == "default_create"))
  
-- | Is r a creation procedure of class c, exported for public creation?
isPublicCreate c r = case [clause | clause <- creates c, routineName r `elem` createNames clause] of
  [] -> null (creates c) && (routineName r == "default_create")
  [clause] -> isPublic (createExportNames clause)
  _ -> error "Routine in multiple create clauses"

-- | classOfType classes cls t: base class for type t in the enclosing class cls, in a system composed of classes
classOfType :: [Clas] -> Clas -> Typ -> (Maybe Clas)
classOfType cs _ (ClassType n _) = listToMaybe (filter ((== n) . className) cs)
classOfType cs c (Like "Current") = Just c
classOfType cs c (Like f) = case typeByName cs c f of
  Nothing -> Nothing
  Just t -> classOfType cs c t
classOfType _ _ _ = Nothing

typeByNameExact :: Clas -> String -> (Maybe Typ)
typeByNameExact cls name =
  case findRoutine cls name of
    Just f -> Just (routineResult f)
    Nothing -> case findAttrInt (clasInterface cls) name of
      Just a -> Just (declType (attrDecl a))
      Nothing -> case findConstantInt (clasInterface cls) name of
        Just c -> Just (declType (constDecl c))
        Nothing -> Nothing
        
-- | Type of feature called name from class cls in a system composed of classes        
typeByName :: [Clas] -> Clas -> String -> (Maybe Typ)
typeByName classes cls name = case catMaybes (typeByNameExact cls name : map inParent (parents classes cls)) of
  [] -> Nothing
  Like "Current":_ -> Just (classToType cls)
  Like f:_ -> typeByName classes cls f
  t:_ -> Just t
  where 
    inParent par = typeByName classes par (unrenamed par cls name)
    
{- MBC utilities -}

-- | List of model queries of cls
modelQueries cls = noteValues modelClause (classNote cls)

-- | Is routine specification-only (ghost)?
isSpecOnly routine = ghostStatus `elem` noteValues statusClause (routineNote routine)

-- | Note clause that make a feature specification-only
specNote = Note statusClause [VarOrCall ghostStatus]

{- Code generation -}

{-- Expressions --}
litBool = attachEmptyPos . LitBool
litVoid = attachEmptyPos LitVoid
currentVar = attachEmptyPos CurrentVar
var = attachEmptyPos . VarOrCall
unqualCall n args = attachEmptyPos $ UnqualCall n args
qualCall t n args = attachEmptyPos $ QualCall t n args
call t n args = case contents t of
  CurrentVar -> case args of
    [] -> var n
    _ -> unqualCall n args
  VarOrCall _ -> qualCall t n args

notExpr = attachEmptyPos . UnOpExpr Not
old = attachEmptyPos . UnOpExpr Old

referenceEqual e1 e2 = attachEmptyPos $ BinOpExpr (RelOp Eq NoType) e1 e2
notEqual e1 e2 = attachEmptyPos $ BinOpExpr (RelOp Neq NoType) e1 e2
andExpr e1 e2 = attachEmptyPos $ BinOpExpr And e1 e2
andThen e1 e2 = attachEmptyPos $ BinOpExpr AndThen e1 e2
implies e1 e2 = attachEmptyPos $ BinOpExpr Implies e1 e2

{-- Statements --}
assign e1 e2 = attachEmptyPos $ Assign e1 e2
callStmt =  attachEmptyPos . CallStmt  
block = attachEmptyPos . Block
