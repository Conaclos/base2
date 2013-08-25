module Main where

import Language.Eiffel.Syntax
import Language.Eiffel.Parser.Parser
import Language.Eiffel.PrettyPrint
import Language.Eiffel.Util
import Language.Eiffel.Position
import Text.Parsec.ByteString
import System.Environment
import System.IO
import System.Directory
import System.FilePath

tempFile = "contracts.e"
  
main = do
  files <- getArgs
  mapM_ go files
  where
    go file = do
      clsE <- parseClassFile file
      case clsE of
        Left err -> print err
        Right cls -> do
          putStr $ className cls ++ " "
          countFiltered cls extractPreconditions expr
          countFiltered cls extractPostconditions expr
          countFiltered cls extractInvariant expr
          countFiltered cls extractNotes note
          countFiltered cls extractSpecRoutines (routineDoc routineBodyDoc)
          countFiltered cls extractExecutable toDoc
          putStr $ (show . length . extractPreconditions) cls ++ " "
          putStr $ (show . length . extractPostconditions) cls ++ " "
          putStr $ (show . length . extractInvariant) cls ++ " "
          putStr $ (show . length . extractModify) cls ++ " "
          putStr $ (show . length . extractSpecRoutines) cls ++ " "
          putStr $ "\n"
    
countFiltered cls filter printer = do
  h <- openFile tempFile WriteMode
  hPrint h (vsep (map printer (filter cls)))
  hClose h
  i <- countTokens tempFile
  putStr (show i ++ " ")
  removeFile tempFile 
  
extractPostconditions :: Clas -> [Expr]
extractPostconditions cls = filter (not . isTrue) (concatMap postFromFeature (allFeatures cls))

postFromFeature :: FeatureEx Expr -> [Expr]
postFromFeature f = map clauseExpr (featurePost f)

extractPreconditions :: Clas -> [Expr]
extractPreconditions cls = filter (not . isTrue) (concatMap preFromFeature (allFeatures cls))

preFromFeature :: FeatureEx Expr -> [Expr]
preFromFeature f = map clauseExpr (featurePre f)

extractInvariant :: Clas -> [Expr]
extractInvariant cls = filter (not . isTrue) (map clauseExpr (invnts cls))
  
extractNotes :: Clas -> [Note]
extractNotes cls = filter isMBCNote (classNote cls ++ concatMap attrNotes (allAttributes cls) ++ concatMap routineNote (allRoutines cls))

extractModify :: Clas -> [Note]
extractModify cls = filter (\n -> noteTag n == "modify") (classNote cls ++ concatMap attrNotes (allAttributes cls) ++ concatMap routineNote (allRoutines cls))

extractSpecRoutines :: Clas -> [Routine]
extractSpecRoutines cls = map stripSpecs $ filter isSpecRoutine (allRoutines cls)

extractExecutable :: Clas -> [Clas]
extractExecutable cls = [cls {
  classNote = filter (not . isMBCNote) (classNote cls),
  featureClauses = filter (not . isEmpty) (map extractFromClause (featureClauses cls)),
  invnts = []
}]
  where
    extractFromClause clause = clause { routines = map stripSpecs $ filter (not . isSpecRoutine) (routines clause) }
    isEmpty clause = null (routines clause) && null (attributes clause) && null (constants clause)

isTrue expr = case contents expr of
  LitBool True -> True
  _ -> False
  
isMBCNote note = noteTag note `elem` ["model", "status", "modify", "open", "dependency"]  

isSpecRoutine r = case filter (\n -> noteTag n == "status") (routineNote r) of
  [] -> False
  [Note _ values] -> (VarOrCall "specification") `elem` values
  
stripSpecs r = r {
  routineReq = Contract True [],
  routineEns = Contract True [],
  routineNote = []
}    