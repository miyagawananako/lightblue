{-# LANGUAGE ScopedTypeVariables #-}
-- | Builds Wani's proof trees from problems and proof terms a language model wrote.
module Main (main) where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate, try, SomeException)
import Control.Monad (forM, forM_)
import qualified Data.List as List
import qualified Data.List.Split as List
import qualified Data.Map.Strict as Map
import Data.Time.Clock (getCurrentTime, diffUTCTime, NominalDiffTime)
import qualified Data.Text.Lazy as TL
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.FilePath ((</>))
import System.Mem (performMajorGC)
import System.Timeout (timeout)
import Text.Printf (printf)
import qualified ListT
import qualified Interface.Tree as I
import qualified Interface.Text as IText
import qualified DTS.QueryTypes as QT
import qualified DTS.DTTdeBruijn as DTT
import qualified DTS.UDTTdeBruijn as UDTT
import qualified DTS.TypeChecker as TC
import qualified DTS.Prover.Wani.BackwardRules as BR
import qualified DTS.Prover.Wani.Prove as Prove
import qualified LlmTerm

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--llm-term-selftest"] -> LlmTerm.llmTermSelfTest
    ("--llm-build":rest) -> llmBuildMain rest
    _ -> error "Usage: llmTerm --llm-term-selftest | --llm-build [--sequential] problems.jsonl outDir"

-- ============================================
-- --llm-build: training data from problems and proof terms a language model wrote
-- ============================================

llmBuildMain :: [String] -> IO ()
llmBuildMain ("--sequential":args) = llmBuild False args
llmBuildMain args = llmBuild True args

-- | The first argument is `QT.concurrent` for both the plain search and the build.
llmBuild :: Bool -> [String] -> IO ()
llmBuild concurrent args = case args of
  [problemsFile, outDir] -> do
    createDirectoryIfMissing True outDir
    problems <- LlmTerm.readProblems problemsFile
    outcomes <- forM (zip [1 :: Int ..] problems) $ \(idx, p) -> case p of
      Left err -> do
        putStrLn $ printf "[%d] not read: %s" idx err
        return (printf "%d\t-\t-\tnot read\t%s" idx (oneLine err), Nothing)
      Right problem -> llmBuildOne concurrent idx problem
    writeFile (outDir </> "results.tsv") $ unlines $
      List.intercalate "\t" ["idx", "name", "logic", "stage", "detail", "search", "searchTime", "trees", "buildTime", "typeCheck", "pairs"]
      : map fst outcomes
    let rules = concat [rs | (_, Just rs) <- outcomes]
        stageCount s = length [() | (row, _) <- outcomes, (List.splitOn "\t" row !! 3) == s]
        labels = Map.fromListWith (+) [ (show l, 1 :: Int) | r <- rules, Just l <- [BR.dttruleToRuleLabel r] ]
    putStrLn ""
    putStrLn $ "Problems:        " ++ show (length outcomes)
    forM_ ["not read", "not converted", "no tree", "tree"] $ \s ->
      putStrLn $ printf "  %-14s %d" (s ++ ":") (stageCount s)
    putStrLn $ "Pairs:           " ++ show (length rules)
    putStrLn $ "Rule labels:     " ++ show (Map.toList labels)
    putStrLn $ "Plain search:    " ++ if concurrent then "concurrent" else "sequential"
  _ -> error "Usage: llmTerm --llm-build [--sequential] problems.jsonl outDir"
  where
    oneLine = map (\c -> if c `elem` ("\t\n\r" :: String) then ' ' else c)

-- | One problem: convert it, record whether plain Wani proves it on its own, and build
-- Wani's tree from the term. Returns the rules of the first tree, one per (Judgment, rule) pair.
llmBuildOne :: Bool -> Int -> LlmTerm.LlmProblem -> IO (String, Maybe [QT.DTTrule])
llmBuildOne concurrent idx problem = do
  let name = LlmTerm.lpName problem
      row stage detail rest = List.intercalate "\t" ([show idx, name, LlmTerm.lpLogic problem, stage, oneLine detail] ++ rest)
  putStr $ printf "[%d] %s: " idx name
  case LlmTerm.elaborateProblem problem of
    Left err -> do
      putStrLn $ "not converted: " ++ err
      return (row "not converted" err ["-", "-", "-", "-", "-", "-"], Nothing)
    Right el -> do
      let query = LlmTerm.elQuery el
          term = LlmTerm.elTerm el
          logic = Just (LlmTerm.elLogic el)
          searchSetting = QT.defaultProofSearchSetting { QT.maxDepth = Just 9, QT.maxTime = Just 30000, QT.logicSystem = logic, QT.concurrent = concurrent }
          buildSetting = searchSetting { QT.maxDepth = Just 15 }
      searched <- try $ timeout (120 * 1000000) (runProveWithTree searchSetting query)
      let (search, searchTime) = case searched of
            Left (_ :: SomeException) -> ("error", "-")
            Right Nothing -> ("timeout", "-")
            Right (Just ([], t)) -> ("not proved", printf "%.3f" (realToFrac t :: Double))
            Right (Just (_, t)) -> ("proved", printf "%.3f" (realToFrac t :: Double))
      start <- getCurrentTime
      built <- try $ timeout (60 * 1000000) $ do
        ts <- Prove.proveWithTerm buildSetting query term
        evaluate (length ts) >> return ts
      end <- getCurrentTime
      typeChecked <- typeCheckProof query term
      let buildTime = printf "%.3f" (realToFrac (diffUTCTime end start) :: Double) :: String
          termText = TL.unpack (IText.toText term)
      case built of
        Right (Just ts@(tree : _)) -> do
          let rules = treeRules tree
          putStrLn $ printf "tree (%d), %d pairs; plain Wani %s" (length ts) (length rules) search
          return ( row "tree" termText [search, searchTime, show (length ts), buildTime, typeChecked, show (length rules)]
                 , Just rules )
        other -> do
          let detail = case other of
                Left (e :: SomeException) -> "error: " ++ takeWhile (/= '\n') (show e)
                Right Nothing -> "timeout"
                _ -> "no tree"
          putStrLn $ printf "%s; plain Wani %s" detail search
          return (row "no tree" (detail ++ ": " ++ termText) [search, searchTime, "0", buildTime, typeChecked, "0"], Nothing)
  where
    oneLine = map (\c -> if c `elem` ("\t\n\r" :: String) then ' ' else c)

-- | Pre-order, the order the training pairs are taken in.
treeRules :: I.Tree QT.DTTrule DTT.Judgment -> [QT.DTTrule]
treeRules t = I.ruleName t : concatMap treeRules (I.daughters t)

runProveWithTree :: QT.ProofSearchSetting -> DTT.ProofSearchQuery
                 -> IO ([I.Tree QT.DTTrule DTT.Judgment], NominalDiffTime)
runProveWithTree setting query@(DTT.ProofSearchQuery sig ctx typ) = do
  -- Keep evaluating the query and collecting garbage out of the measured time.
  evaluate $ rnf (sig, ctx, typ)
  performMajorGC
  startTime <- getCurrentTime
  maybeTree <- ListT.head (Prove.prove' setting query)
  endTime <- getCurrentTime
  return (maybe [] (: []) maybeTree, diffUTCTime endTime startTime)

-- | The type checker throws its failure messages away (list-t's fail), so
-- only the outcome is reported.
typeCheckProof :: DTT.ProofSearchQuery -> DTT.Preterm -> IO String
typeCheckProof (DTT.ProofSearchQuery sig ctx goal) term = do
  let query = UDTT.toUDTTJudgment (DTT.Judgment sig ctx term goal)
      checker = TC.typeCheck (TC.nullProver QT.defaultProofSearchSetting) False
  r <- try $ timeout (60 * 1000000) $ ListT.head (checker query)
  return $ case r of
    Left (e :: SomeException) -> "error: " ++ map (\c -> if c `elem` ("\t\n\r" :: String) then ' ' else c) (show e)
    Right Nothing             -> "timeout"
    Right (Just Nothing)      -> "rejected"
    Right (Just (Just _))     -> "accepted"
