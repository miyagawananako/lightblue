{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
-- | Problems and proof terms written by a language model as S-expressions with named
-- variables (the syntax in the generation prompt), read into DTT in the forms Wani
-- builds its own proofs with, so that Wani can rebuild its proof tree from the term.
module LlmTerm
  ( LlmProblem(..)
  , Elaborated(..)
  , readProblems
  , elaborateProblem
  , llmTermSelfTest
  ) where

import Control.Monad (foldM, forM, forM_, unless, when)
import Control.Exception (evaluate, try, SomeException)
import Data.List (elemIndex)
import qualified Data.Aeson as Aeson
import Data.Aeson ((.:))
import qualified Data.ByteString.Lazy.Char8 as BLC
import qualified Data.Text.Lazy as TL
import System.Timeout (timeout)
import Text.Parsec (between, char, eof, many, many1, noneOf, parse, spaces, (<|>))
import Text.Parsec.String (Parser)
import qualified DTS.DTTdeBruijn as DTT
import qualified DTS.QueryTypes as QT
import qualified DTS.Prover.Wani.Prove as Prove
import qualified Interface.Text as IText
import qualified Interface.Tree as I
import qualified ListT

data LlmProblem = LlmProblem
  { lpName        :: String
  , lpDescription :: String
  , lpLogic       :: String
  , lpSignature   :: [(String, String)]
  , lpContext     :: [(String, String)]   -- ^ first hypothesis first
  , lpGoal        :: String
  , lpTerm        :: String
  }

instance Aeson.FromJSON LlmProblem where
  parseJSON = Aeson.withObject "problem" $ \o -> LlmProblem
    <$> o .: "name" <*> o .: "description" <*> o .: "logic"
    <*> o .: "signature" <*> o .: "context" <*> o .: "goal" <*> o .: "term"

-- | One JSON object per line; a line that does not decode is kept as its error.
readProblems :: FilePath -> IO [Either String LlmProblem]
readProblems path =
  map Aeson.eitherDecode . filter (not . BLC.null) . BLC.lines <$> BLC.readFile path

data Elaborated = Elaborated
  { elLogic :: QT.LogicSystem
  , elQuery :: DTT.ProofSearchQuery
  , elTerm  :: DTT.Preterm
  }

-- ============================================
-- S-expressions
-- ============================================

data SExpr = Atom String | List [SExpr] deriving (Eq)

instance Show SExpr where
  show (Atom a) = a
  show (List xs) = "(" ++ unwords (map show xs) ++ ")"

parseSExpr :: String -> Either String SExpr
parseSExpr s = either (Left . show) Right $ parse (spaces *> sexpr <* eof) "" s
  where
    sexpr :: Parser SExpr
    sexpr = (list <|> atom) <* spaces
    list = List <$> between (char '(' *> spaces) (char ')') (many sexpr)
    atom = Atom <$> many1 (noneOf "() \t\r\n")

keywords :: [String]
keywords =
  [ "type", "entity", "false", "true", "pi", "forall", "->", "sigma", "exists", "and"
  , "or", "not", "iff", "=", "lam", "pair", "fst", "snd", "unit", "inl", "inr", "case"
  , "efq", "dne", "refl", "sym", "trans", "rewrite" ]

-- ============================================
-- Names and types in scope
-- ============================================

-- | The type of a binder is relative to the binders after it, as in a DTT context.
data Binder = Binder (Maybe String) (Maybe DTT.Preterm)

data Env = Env
  { envSig      :: [(String, DTT.Preterm)]
  , envBinders  :: [Binder]               -- ^ innermost first, so index = de Bruijn index
  }

bind :: Maybe String -> Maybe DTT.Preterm -> Env -> Env
bind x t env = env { envBinders = Binder x t : envBinders env }

lookupName :: Env -> String -> Either String DTT.Preterm
lookupName env x
  | x `elem` keywords = Left ("keyword used as a name: " ++ x)
  | Just i <- elemIndex (Just x) [n | Binder n _ <- envBinders env] = Right (DTT.Var i)
  | Just _ <- lookup x (envSig env) = Right (DTT.Con (TL.pack x))
  | otherwise = Left ("unknown name: " ++ x)

-- | Only the shapes the conversion needs: variables, constants, applications, projections.
typeOf :: Env -> DTT.Preterm -> Maybe DTT.Preterm
typeOf env t = case t of
  DTT.Var i -> case drop i (envBinders env) of
    Binder _ (Just ty) : _ -> Just (DTT.shiftIndices ty (i + 1) 0)
    _ -> Nothing
  DTT.Con c -> lookup (TL.unpack c) (envSig env)
  DTT.App f x -> case typeOf env f of
    Just (DTT.Pi _ b) -> Just (instantiate b x)
    _ -> Nothing
  DTT.Proj DTT.Fst m -> case typeOf env m of
    Just (DTT.Sigma a _) -> Just a
    _ -> Nothing
  DTT.Proj DTT.Snd m -> case typeOf env m of
    Just (DTT.Sigma _ b) -> Just (instantiate b (DTT.Proj DTT.Fst m))
    _ -> Nothing
  _ -> Nothing

-- | b[x/0] for b under one binder, lowering the indices above it as betaReduce does
-- (the type checker's subst alone leaves them one too high).
instantiate :: DTT.Preterm -> DTT.Preterm -> DTT.Preterm
instantiate b x = DTT.betaReduce $ DTT.shiftIndices (DTT.subst b (DTT.shiftIndices x 1 0) 0) (-1) 0

-- ============================================
-- Types
-- ============================================

convType :: Env -> SExpr -> Either String DTT.Preterm
convType env e = case e of
  Atom "type" -> Right DTT.Type
  Atom "entity" -> Right DTT.Entity
  Atom "false" -> Right DTT.Bot
  Atom "true" -> Right DTT.Top
  Atom x -> lookupName env x
  List [Atom q, Atom x, a, b] | q `elem` ["pi", "forall"] -> binder DTT.Pi x a b
  List [Atom q, Atom x, a, b] | q `elem` ["sigma", "exists"] -> binder DTT.Sigma x a b
  List (Atom "->" : as@(_:_:_)) -> nondependent DTT.Pi env as
  List (Atom "and" : as@(_:_:_)) -> nondependent DTT.Sigma env as
  List [Atom "or", a, b] -> DTT.Disj <$> convType env a <*> convType env b
  List [Atom "not", a] -> (\a' -> DTT.Pi a' DTT.Bot) <$> convType env a
  List [Atom "iff", a, b] ->
    convType env (List [Atom "and", List [Atom "->", a, b], List [Atom "->", b, a]])
  List [Atom "=", s, t] -> DTT.Eq DTT.Entity <$> convType env s <*> convType env t
  -- An existential witness such as (fst h) can appear inside a type.
  List [Atom p, _] | p `elem` ["fst", "snd"] -> fst <$> elab env e Nothing
  List (Atom f : args) | f `notElem` keywords -> do
    f' <- lookupName env f
    foldl DTT.App f' <$> mapM (convType env) args
  _ -> Left ("not a type: " ++ show e)
  where
    binder k x a b = do
      a' <- convType env a
      k a' <$> convType (bind (Just x) (Just a') env) b

nondependent :: (DTT.Preterm -> DTT.Preterm -> DTT.Preterm) -> Env -> [SExpr] -> Either String DTT.Preterm
nondependent _ env [a] = convType env a
nondependent k env (a : rest) = do
  a' <- convType env a
  k a' <$> nondependent k (bind Nothing (Just a') env) rest
nondependent _ _ [] = Left "empty connective"

-- ============================================
-- Proof terms
-- ============================================

-- | Converts a proof term, checking it against the expected type where one is known
-- and inferring otherwise; the types only guide the conversion (lambdas carry no
-- annotation, and rewriting needs the type it rewrites). Wani checks the result.
elab :: Env -> SExpr -> Maybe DTT.Preterm -> Either String (DTT.Preterm, Maybe DTT.Preterm)
elab env e expected = case e of
  List [Atom "lam", Atom x, m] -> case expected of
    Just (DTT.Pi a b) -> do
      (m', _) <- elab (bind (Just x) (Just a) env) m (Just b)
      Right (DTT.Lam m', expected)
    _ -> do
      (m', _) <- elab (bind (Just x) Nothing env) m Nothing
      Right (DTT.Lam m', Nothing)
  List (Atom "pair" : ms@(_:_:_)) -> pairs ms expected
  List [Atom "fst", m] -> do
    (m', t) <- elab env m Nothing
    Right (DTT.Proj DTT.Fst m', case t of Just (DTT.Sigma a _) -> Just a; _ -> Nothing)
  List [Atom "snd", m] -> do
    (m', t) <- elab env m Nothing
    Right (DTT.Proj DTT.Snd m', case t of
      Just (DTT.Sigma _ b) -> Just (instantiate b (DTT.Proj DTT.Fst m'))
      _ -> Nothing)
  Atom "unit" -> Right (DTT.Unit, Just DTT.Top)
  List [Atom "inl", m] -> injection DTT.Fst m (case expected of Just (DTT.Disj a _) -> Just a; _ -> Nothing)
  List [Atom "inr", m] -> injection DTT.Snd m (case expected of Just (DTT.Disj _ b) -> Just b; _ -> Nothing)
  List [Atom "case", l, c, m, n] -> do
    (l', lt) <- elab env l Nothing
    c' <- convType env c
    let branch a = Just (DTT.Pi a (DTT.shiftIndices c' 1 0))
        (mt, nt) = case lt of Just (DTT.Disj a b) -> (branch a, branch b); _ -> (Nothing, Nothing)
    (m', _) <- elab env m mt
    (n', _) <- elab env n nt
    -- Wani puts the proof of the disjunction first (its unpack is unpack(L, P, M, N)).
    Right (DTT.Unpack l' (DTT.Lam (DTT.shiftIndices c' 1 0)) m' n', Just c')
  List [Atom "efq", m] -> do
    (m', _) <- elab env m (Just DTT.Bot)
    Right (DTT.App (DTT.Con " efq ") m', expected)
  List [Atom "dne", m] -> do
    (m', _) <- elab env m (fmap (\a -> DTT.Pi (DTT.Pi a DTT.Bot) DTT.Bot) expected)
    Right (DTT.App (DTT.Con " dne ") m', expected)
  List [Atom "refl", t] -> do
    t' <- convType env t
    Right (reflAt DTT.Entity t', Just (DTT.Eq DTT.Entity t' t'))
  List [Atom "sym", eq] -> do
    (eq', (s, t)) <- equation eq
    Right (symTerm s t eq', Just (DTT.Eq DTT.Entity t s))
  List [Atom "trans", eq1, eq2] -> do
    (eq1', (s, t)) <- equation eq1
    (eq2', (_, u)) <- equation eq2
    Right (transTerm s t u eq1' eq2', Just (DTT.Eq DTT.Entity s u))
  List [Atom "rewrite", eq, h] -> do
    (eq', (s, t)) <- equation eq
    rewriteTerm env s t eq' h
  Atom x -> do
    v <- lookupName env x
    Right (v, typeOf env v)
  List (f : args) | not (isKeyword f) -> do
    (f', ft) <- elab env f Nothing
    foldM applyArg (f', ft) args
  _ -> Left ("not a proof term: " ++ show e)
  where
    isKeyword (Atom a) = a `elem` keywords
    isKeyword _ = False
    applyArg (f', Just (DTT.Pi a b)) arg = do
      (arg', _) <- elab env arg (Just a)
      Right (DTT.App f' arg', Just (instantiate b arg'))
    applyArg (f', _) arg = do
      (arg', _) <- elab env arg Nothing
      Right (DTT.App f' arg', Nothing)
    pairs [m] t = elab env m t
    pairs (m : rest) t = case t of
      Just (DTT.Sigma a b) -> do
        (m', _) <- elab env m (Just a)
        (n', _) <- pairs rest (Just (instantiate b m'))
        Right (DTT.Pair m' n', t)
      _ -> do
        (m', _) <- elab env m Nothing
        (n', _) <- pairs rest Nothing
        Right (DTT.Pair m' n', Nothing)
    pairs [] _ = Left "empty pair"
    injection sel m t = do
      (m', _) <- elab env m t
      Right (DTT.Iota sel m', expected)
    equation eq = do
      (eq', et) <- elab env eq Nothing
      case et of
        Just (DTT.Eq _ s t) -> Right (eq', (s, t))
        _ -> Left ("not a proof of an equation: " ++ show eq)

-- ============================================
-- Equality in Wani's forms
-- ============================================
-- Wani proves x = x with forwardEqIntro : Π(A:type)(x:A). x =_A x, and rewrites with
-- eqElim h, which it derives for each h in context (Forward.eqForward2): eqElim h
-- takes, binder by binder of h's type, a pair (new, new = old) for each place in the
-- binder's domain and then the binder's argument, and finally a pair for each place in
-- the body, left to right. A place is a term of an object type (an individual or a
-- function on individuals), as in Forward.forEq.

eqElim, forwardEqIntro :: DTT.Preterm
eqElim = DTT.Con "eqElim"
forwardEqIntro = DTT.Con "forwardEqIntro"

apps :: DTT.Preterm -> [DTT.Preterm] -> DTT.Preterm
apps = foldl DTT.App

reflAt :: DTT.Preterm -> DTT.Preterm -> DTT.Preterm
reflAt ty x = apps forwardEqIntro [ty, x]

-- | From e : s = t, t = s: rewrite the right side of t = t to s. This is Wani's own proof.
symTerm :: DTT.Preterm -> DTT.Preterm -> DTT.Preterm -> DTT.Preterm
symTerm s t e = apps eqElim [forwardEqIntro, DTT.Entity, t, t, reflAt DTT.Entity t, s, e]

-- | From e1 : s = t and e2 : t = u, s = u, rewriting both sides of t = t so that
-- neither proof has to be one Wani can derive eqElim for.
transTerm :: DTT.Preterm -> DTT.Preterm -> DTT.Preterm -> DTT.Preterm -> DTT.Preterm -> DTT.Preterm
transTerm s t u e1 e2 = apps eqElim [forwardEqIntro, DTT.Entity, t, s, e1, u, symTerm t u e2]

-- | Rewrites every s to t in the type of h, given e : s = t.
rewriteTerm :: Env -> DTT.Preterm -> DTT.Preterm -> DTT.Preterm -> SExpr
            -> Either String (DTT.Preterm, Maybe DTT.Preterm)
rewriteTerm env s t e h = do
  let (headExpr, args) = case h of
        List (f@(Atom a) : xs) | a `notElem` keywords -> (f, xs)
        _ -> (h, [])
  (hd, hdType) <- elab env headExpr Nothing
  unless (isForwardable hd) $ Left ("rewrite needs a hypothesis or its projection: " ++ show headExpr)
  ty <- maybe (Left ("cannot infer the type of " ++ show headExpr)) Right hdType
  (pieces, body) <- walk [] ty args
  unless (isAtomic body) $ Left ("rewrite target is not atomic: " ++ show h)
  let rewritten = replace s t body
  when (rewritten == body) $ Left ("nothing to rewrite in " ++ show h)
  Right (apps (DTT.App eqElim hd) pieces, Just rewritten)
  where
    isForwardable (DTT.Var _) = True
    isForwardable (DTT.Proj _ m) = isForwardable m
    isForwardable _ = False
    newEqOld = symTerm s t e
    -- `instantiated` holds the arguments given so far, innermost first, in env's scope;
    -- places are found in the uninstantiated type, as forEq sees it.
    walk instantiated ty [] =
      Right (places instantiated ty ((== s) . close instantiated), close instantiated ty)
    walk instantiated (DTT.Pi a b) (x : xs) = do
      (x', _) <- elab env x (Just (close instantiated a))
      (rest, body) <- walk (x' : instantiated) b xs
      Right (places instantiated a (const False) ++ [x'] ++ rest, body)
    walk _ ty _ = Left ("too many arguments for " ++ TL.unpack (IText.toText ty))
    close instantiated ty = foldl (\body (k, x) -> instantiate body (DTT.shiftIndices x k 0)) ty
                              (zip [length instantiated - 1, length instantiated - 2 ..] instantiated)
    places instantiated term rewriteHere = go term
      where
        lenv = foldl (\en _ -> bind Nothing Nothing en) env instantiated
        go m
          | isObject m && rewriteHere m = [t, newEqOld]
          | DTT.App f x <- m = go f ++ go x
          | DTT.Eq _ l r <- m = go l ++ go r
          | isObject m = let v = close instantiated m in [v, reflAt (objectType v) v]
          | otherwise = []
        isObject m = maybe False isObjectType (typeOfLocal m)
        typeOfLocal m = case m of
          DTT.Var i | i < length instantiated -> typeOf env (instantiated !! i)
          _ -> typeOf lenv m
        objectType v = maybe DTT.Entity id (typeOf env v)

isObjectType :: DTT.Preterm -> Bool
isObjectType DTT.Entity = True
isObjectType (DTT.Pi DTT.Entity b) = isObjectType b
isObjectType _ = False

isAtomic :: DTT.Preterm -> Bool
isAtomic t = case t of
  DTT.Eq {} -> True
  DTT.App f _ -> isAtomic' f
  DTT.Con _ -> True
  DTT.Var _ -> True
  _ -> False
  where
    isAtomic' (DTT.App f _) = isAtomic' f
    isAtomic' (DTT.Con _) = True
    isAtomic' (DTT.Var _) = True
    isAtomic' _ = False

replace :: DTT.Preterm -> DTT.Preterm -> DTT.Preterm -> DTT.Preterm
replace s t m
  | m == s = t
  | otherwise = case m of
      DTT.App f x -> DTT.App (replace s t f) (replace s t x)
      DTT.Eq a l r -> DTT.Eq a (replace s t l) (replace s t r)
      _ -> m

-- ============================================
-- Problems
-- ============================================

elaborateProblem :: LlmProblem -> Either String Elaborated
elaborateProblem p = do
  logic <- case lpLogic p of
    "intuitionistic" -> Right QT.Intuitionistic
    "classical" -> Right QT.Classical
    l -> Left ("unknown logic: " ++ l)
  sig <- forM (lpSignature p) $ \(name, tyStr) -> do
    when (name `elem` keywords) $ Left ("keyword used as a name: " ++ name)
    ty <- parseSExpr tyStr >>= convType (Env [] [])
    unless (signatureType ty) $ Left ("not a constant's type: " ++ name ++ " : " ++ tyStr)
    Right (name, ty)
  let env0 = Env sig []
  (env, ctx) <- foldM (\(en, acc) (name, tyStr) -> do
                         ty <- parseSExpr tyStr >>= convType en
                         Right (bind (Just name) (Just ty) en, ty : acc))
                      (env0, []) (lpContext p)
  goal <- parseSExpr (lpGoal p) >>= convType env
  termExpr <- parseSExpr (lpTerm p)
  let usesDne = Atom "dne" `elem` atoms termExpr
  when (usesDne /= (logic == QT.Classical)) $ Left "logic does not match the use of dne"
  (term, _) <- elab env termExpr (Just goal)
  Right Elaborated
    { elLogic = logic
    , elQuery = DTT.ProofSearchQuery [(TL.pack n, t) | (n, t) <- sig] ctx goal
    , elTerm = term
    }
  where
    atoms (List xs) = concatMap atoms xs
    atoms a = [a]

-- | Constants only: propositions, individuals, predicates and functions on individuals.
signatureType :: DTT.Preterm -> Bool
signatureType t = case t of
  DTT.Type -> True
  DTT.Entity -> True
  DTT.Pi DTT.Entity b -> signatureType b
  _ -> False

-- ============================================
-- --llm-term-selftest
-- ============================================

-- | Small problems in the prompt's syntax (equality, and disjunction elimination),
-- with Wani's own proof term where the conversion is meant to give the same one.
selfTestCases :: [(LlmProblem, Maybe String)]
selfTestCases =
  [ (problem "subst" [("h", "(P a)"), ("e", "(= a b)")] "(P b)" "(rewrite e h)",
     Just "(((eqElim 1) b) (((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 0))")
  , (problem "sym" [("e", "(= a b)")] "(= b a)" "(sym e)",
     Just "(((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 0)")
  , (problem "trans" [("e1", "(= a b)"), ("e2", "(= b c)")] "(= a c)" "(trans e1 e2)", Nothing)
  , (problem "both-sides" [("h", "(R a a)"), ("e", "(= a b)")] "(R b b)" "(rewrite e h)",
     Just "(((((eqElim 1) b) (((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 0)) b) (((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 0))")
  , (problem "under-forall" [("h", "(forall y entity (R a y))"), ("e", "(= a b)")]
       "(forall z entity (R b z))" "(lam w (rewrite e (h w)))",
     Just "λ.((((((eqElim 2) 0) b) (((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 1)) 0) ((forwardEqIntro entity) 0))")
  , (problem "in-function" [("h", "(P (f a))"), ("e", "(= a b)")] "(P (f b))" "(rewrite e h)",
     Just "(((((eqElim 1) f) ((forwardEqIntro (Π entity)entity) f)) b) (((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 0))")
  , (problem "eq-itself" [("h", "(= a c)"), ("e", "(= a b)")] "(= b c)" "(rewrite e h)",
     Just "(((((eqElim 1) b) (((((((eqElim forwardEqIntro) entity) b) b) ((forwardEqIntro entity) b)) a) 0)) c) ((forwardEqIntro entity) c))")
  , (problem "compound-side" [("h", "(P (f a))"), ("e", "(= (f a) b)")] "(P b)" "(rewrite e h)", Nothing)
  , (problem "applied-hypothesis" [("h", "(forall x entity (-> (Q x) (P (f x))))"), ("hq", "(Q a)"), ("e", "(= (f a) b)")]
       "(P b)" "(rewrite e (h a hq))", Nothing)
  , (problem "imp-const" [("h", "(-> (Q a) (P a))"), ("hq", "(Q a)"), ("e", "(= a b)")]
       "(P b)" "(rewrite e (h hq))", Nothing)
  , (problem "forall-imp" [("h", "(forall x entity (-> (Q x) (P x)))"), ("hq", "(Q a)"), ("e", "(= a b)")]
       "(P b)" "(rewrite e (h a hq))", Nothing)
  , (problem "forall-prop-imp" [("h", "(forall x entity (-> p (P x)))"), ("hp", "p"), ("e", "(= a b)")]
       "(P b)" "(rewrite e (h a hp))", Nothing)
  , (problem "case-context" [("h", "(or (P a) (Q a))"), ("hp", "(-> (P a) p)"), ("hq", "(-> (Q a) p)")]
       "p" "(case h p (lam u (hp u)) (lam v (hq v)))", Nothing)
  , (problem "case-forall" [("h", "(forall x entity (or (P x) (Q x)))"), ("hp", "(forall y entity (-> (P y) p))")
       , ("hq", "(forall z entity (-> (Q z) p))")]
       "p" "(case (h a) p (lam u (hp a u)) (lam v (hq a v)))", Nothing)
  , (problem "case-var-result" []
       "(forall x entity (-> (or (P x) (Q x)) (or (Q x) (P x))))"
       "(lam x (lam h (case h (or (Q x) (P x)) (lam u (inr u)) (lam v (inl v)))))", Nothing)
  , (problem "case-var-disj" []
       "(forall x entity (-> (or (P x) (Q x)) (-> (P x) p) (-> (Q x) p) p))"
       "(lam x (lam h (lam hp (lam hq (case h p (lam u (hp u)) (lam v (hq v)))))))", Nothing)
  ]
  where
    problem name ctx goal term = LlmProblem name "" "intuitionistic"
      [ ("p", "type"), ("a", "entity"), ("b", "entity"), ("c", "entity"), ("P", "(-> entity type)")
      , ("Q", "(-> entity type)"), ("R", "(-> entity entity type)"), ("f", "(-> entity entity)") ]
      ctx goal term

llmTermSelfTest :: IO ()
llmTermSelfTest = forM_ selfTestCases $ \(p, expected) -> do
  putStrLn $ "== " ++ lpName p
  case elaborateProblem p of
    Left err -> putStrLn $ "  conversion failed: " ++ err
    Right el -> do
      let termText = TL.unpack (IText.toText (elTerm el))
      putStrLn $ "  term: " ++ termText
      forM_ expected $ \w -> putStrLn $ "  same as Wani's: " ++ show (termText == w)
      let setting = QT.defaultProofSearchSetting
            { QT.maxDepth = Just 15, QT.maxTime = Just 30000, QT.logicSystem = Just (elLogic el) }
      built <- try $ timeout (60 * 1000000) $ do
        ts <- Prove.proveWithTerm setting (elQuery el) (elTerm el)
        evaluate (length ts)
      putStrLn $ "  with term: " ++ case built of
        Left (ex :: SomeException) -> "error: " ++ takeWhile (/= '\n') (show ex)
        Right Nothing -> "timeout"
        Right (Just n) -> show n ++ " tree(s)"
      -- Where no term of Wani's is written down yet, show the one it finds.
      when (expected == Nothing) $ do
        found <- try $ timeout (60 * 1000000) $
          ListT.head (Prove.prove' setting { QT.maxDepth = Just 9 } (elQuery el))
        putStrLn $ "  wani's: " ++ case found of
          Left (ex :: SomeException) -> "error: " ++ takeWhile (/= '\n') (show ex)
          Right Nothing -> "timeout"
          Right (Just Nothing) -> "not proved"
          Right (Just (Just tree)) -> TL.unpack (IText.toText (DTT.trm (I.node tree)))
