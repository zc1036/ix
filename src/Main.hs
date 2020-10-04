
module Main where

import Parser (parseToplevel, SExpr(IntLiteral, FloatLiteral, SymbolLiteral, StringLiteral, Cons, Nil), sexprdata)
import Data.List (intercalate)
import Control.Monad.State
import Data.Map (Map, toList, fromList, empty, (!), lookup, insert)
import ReversibleMap (RMap, rempty, rlookup, rassociate, rinsert, rtoList)
import Data.Maybe (fromMaybe)
import Text.Printf
import Debug.Trace (trace)

type TypeVar = Int
type Unification = Map TypeVar Type

data CState = CState { nextTypeVar :: TypeVar,
                       symbolTypeVars :: Map String TypeVar,
                       unified :: RMap TypeVar Type }

newstate :: CState
newstate = CState { nextTypeVar = 1,
                    symbolTypeVars = empty,
                    unified = rempty }

cNextTypeVar :: State CState TypeVar
cNextTypeVar = do
  state@(CState { nextTypeVar=id }) <- get
  put $ state { nextTypeVar = id + 1 }
  return id

cSymbolVar :: String -> State CState TypeVar
cSymbolVar name = do
  CState { symbolTypeVars=typeVars } <- get
  case Data.Map.lookup name typeVars of
    Just id -> return id
    Nothing -> do
        newId <- cNextTypeVar
        state <- get
        put $ state { symbolTypeVars=(insert name newId typeVars) }
        return newId

cUnification :: State CState [(TypeVar, Int, Maybe Type)]
cUnification = do
  state <- get
  return $ rtoList $ unified state -- toList $ unified state

cUnifiedType :: TypeVar -> State CState (Maybe Type)
cUnifiedType i = do
  state <- get
  return $ rlookup i (unified state)

cRemapsTo :: TypeVar -> TypeVar -> State CState ()
cRemapsTo i j = do
  state@(CState { unified=rm }) <- get
  put $ state { unified = rassociate j i rm }

cMapsTo :: TypeVar -> Type -> State CState ()
cMapsTo i t = do
  state@(CState { unified = m }) <- get
  put $ state { unified = rinsert i t m }

cAddDupintConstraint :: String -> State CState Constraints
cAddDupintConstraint name = do
  dupid <- cSymbolVar name
  argtuple <- cNextTypeVar
  argtuple2 <- cNextTypeVar
  rettuple <- cNextTypeVar
  rettuple2 <- cNextTypeVar
  rettuple3 <- cNextTypeVar
  inttype <- cNextTypeVar
  return $ [ C_VarIs dupid $ T_Function argtuple rettuple
           , C_VarIs inttype T_Int64
           , C_VarIs argtuple $ T_Tuple inttype argtuple2
           , C_VarIs rettuple $ T_Tuple inttype rettuple2
           , C_VarIs rettuple2 $ T_Tuple inttype rettuple3
           , C_VarEqual rettuple3 argtuple2 ]
  
cAddArithmeticConstraint :: String -> State CState Constraints
cAddArithmeticConstraint name = do
  dupid <- cSymbolVar name
  argtuple <- cNextTypeVar
  argtuple2 <- cNextTypeVar
  argtuple3 <- cNextTypeVar
  rettuple <- cNextTypeVar
  rettuple2 <- cNextTypeVar
  inttype <- cNextTypeVar
  return $ [ C_VarIs dupid $ T_Function argtuple rettuple
           , C_VarIs inttype T_Int64
           , C_VarIs argtuple $ T_Tuple inttype argtuple2
           , C_VarIs argtuple2 $ T_Tuple inttype argtuple3
           , C_VarIs rettuple $ T_Tuple inttype rettuple2
           , C_VarEqual argtuple3 rettuple2 ]

cAddLambdaConstraint :: State CState Constraints
cAddLambdaConstraint = do
  dupid <- cSymbolVar "λ"
  argtuple <- cNextTypeVar
  argtuple2 <- cNextTypeVar
  argtuple3 <- cNextTypeVar
  rettuple <- cNextTypeVar
  rettuple2 <- cNextTypeVar
  inttype <- cNextTypeVar
  return $ [ C_VarIs dupid $ T_Function argtuple rettuple
           , C_VarIs inttype T_Int64
           , C_VarIs argtuple $ T_Tuple inttype argtuple2
           , C_VarIs argtuple2 $ T_Tuple inttype argtuple3
           , C_VarIs rettuple $ T_Tuple inttype rettuple2
           , C_VarEqual argtuple3 rettuple2 ]

cAddDefaultConstraints :: State CState Constraints
cAddDefaultConstraints = do
  c1 <- cAddDupintConstraint "dupint"
  c2 <- cAddDupintConstraint "dupint2"
  c3 <- cAddArithmeticConstraint "+"
  c4 <- cAddArithmeticConstraint "*"
  c5 <- cAddLambdaConstraint
  return $ c1 ++ c2 ++ c3 ++ c4

exprid = sexprdata

data Type = T_Unit
          | T_Int64
          | T_Float
          | T_String
          | T_Tuple TypeVar TypeVar
          | T_Function TypeVar TypeVar
            deriving (Show)

tshow :: Type -> String
tshow (T_Function a r) = "T_Function T" ++ (show a) ++ " T" ++ (show r)
tshow (T_Tuple a r) = "T_Tuple T" ++ (show a) ++ " T" ++ (show r)
tshow x = show x

unconstrainedVarString = "_"

pprintType :: Type -> State CState String
pprintType T_Unit = return "()"
pprintType T_Float = return "Float"
pprintType T_Int64 = return "Int64"
pprintType T_String = return "String"
pprintType (T_Tuple l r) = do
  tl <- cUnifiedType l
  tr <- cUnifiedType r
  tl' <- pprintTypeMaybe unconstrainedVarString tl
  tr' <- pprintTypeMaybe unconstrainedVarString tr
  return $ "(T" ++ (show l) ++ "=" ++ tl' ++ ", T" ++ (show r) ++ "=" ++ tr' ++ ")"
pprintType (T_Function l r) = do
  tl <- cUnifiedType l
  tr <- cUnifiedType r
  tl' <- pprintTypeMaybe unconstrainedVarString tl
  tr' <- pprintTypeMaybe unconstrainedVarString tr
  return $ "(T" ++ (show l) ++ "=" ++ tl' ++ " -> T" ++ (show r) ++ "=" ++ tr' ++ ")"

pprintTypeMaybe :: String -> Maybe Type -> State CState String
pprintTypeMaybe def Nothing = return def
pprintTypeMaybe _ (Just t) = pprintType t

data TypeAssertion = C_VarEqual TypeVar TypeVar
                   | C_VarIs TypeVar Type

instance Show TypeAssertion where
    show (C_VarEqual i j) = "T" ++ (show i) ++ " = T" ++ (show j)
    show (C_VarIs i t) = "T" ++ (show i) ++ " = Type(" ++ (tshow t) ++ ")"

type Constraints = [TypeAssertion]

{-
literalConstraints :: TypeVar -> Type -> State CState Constraints
literalConstraints id t = do
  argtuple <- cNextTypeVar
  rettuple <- cNextTypeVar
  littype <- cNextTypeVar
  return [ C_VarIs littype t
         , C_VarIs rettuple $ T_Tuple littype argtuple
         , C_VarIs id $ T_Function argtuple rettuple ]
-}

findNil :: SExpr Int -> SExpr Int
findNil (Cons _ l _) = findNil l
findNil n@(Nil _) = n
findNil _ = error "Cannot find nil in list"

literalConstraints :: TypeVar -> Type -> State CState Constraints
literalConstraints id t = 
    return [ C_VarIs id t ]

literalConsConstraints :: SExpr TypeVar -> State CState Constraints
literalConsConstraints (Cons id l (Cons fid cl cr)) = do
  clconstraints <- constraints cl
  crconstraints <- constraints cr
  lconstraints <- constraints l
  fnret <- cNextTypeVar
  return $ (clconstraints
            ++ crconstraints
            ++ lconstraints
            ++ [ C_VarIs id $ T_Tuple fid (sexprdata l)
               -- cr will return its entire stack, which is
               -- why we can use its return type as the    
               -- return type of the lambda
               , C_VarIs (sexprdata cr) $ T_Function (sexprdata cl) fnret
               , C_VarIs fid $ T_Function (sexprdata (findNil cl)) (sexprdata cr) ])

literalConsConstraints (Cons id l r) = do
  lconstraints <- constraints l
  rconstraints <- constraints r
  return $ (lconstraints
            ++ rconstraints
            ++ [ C_VarIs id $ T_Tuple (sexprdata r) (sexprdata l) ])

constraints :: SExpr TypeVar -> State CState Constraints
constraints (IntLiteral id _) = literalConstraints id T_Int64
constraints (FloatLiteral id _) = literalConstraints id T_Float
constraints (StringLiteral id _) = literalConstraints id T_String
constraints (SymbolLiteral id sym) = do
  symVar <- cSymbolVar sym
  return [ C_VarEqual symVar id ]
constraints (Nil id) = do
  return [ ] -- Nil is unconstrained since it's the "input goes here"
             -- terminal for functions
constraints (Cons id l r@(SymbolLiteral _ _)) = do
  lconstraints <- constraints l
  rconstraints <- constraints r
  return $ (lconstraints
            ++ rconstraints
            ++ [ C_VarIs (sexprdata r) $ T_Function (sexprdata l) id ])
constraints c@(Cons _ _ _) = literalConsConstraints c

equalTypes :: Type -> Type -> State CState ()
equalTypes T_Unit T_Unit = return ()
equalTypes T_Int64 T_Int64 = return ()
equalTypes T_Float T_Float = return ()
equalTypes T_String T_String = return ()
equalTypes (T_Tuple t1a t1b) (T_Tuple t2a t2b) = do
  applyConstraint $ C_VarEqual t1a t2a
  applyConstraint $ C_VarEqual t1b t2b
equalTypes (T_Function t1a t1b) (T_Function t2a t2b) = do
  applyConstraint $ C_VarEqual t1a t2a
  applyConstraint $ C_VarEqual t1b t2b
equalTypes a b = error $ "Cannot unify types " ++ (tshow a) ++ " and " ++ (tshow b)

applyConstraint :: TypeAssertion -> State CState ()
applyConstraint (C_VarEqual i j) =
  if i == j then
      return ()
  else do
    t1 <- cUnifiedType i
    t2 <- cUnifiedType j
    case (t1, t2) of
      (Nothing, Nothing) ->
          i `cRemapsTo` j
      (Nothing, Just _) ->
          i `cRemapsTo` j
      (Just _, Nothing) ->
          j `cRemapsTo` i
      (Just t1, Just t2) ->
          equalTypes t1 t2
applyConstraint (C_VarIs i t) = do
  mt' <- cUnifiedType i
  case mt' of
    Nothing -> i `cMapsTo` t
    Just t' -> equalTypes t' t

unify :: Constraints -> State CState ()
unify [] = return ()
unify (x:xs) = do
  applyConstraint x
  unify xs

simpleAssignExprId :: (TypeVar -> a -> SExpr TypeVar) -> a -> State CState (SExpr TypeVar)
simpleAssignExprId genSExpr v = do
  nid <- cNextTypeVar
  return $ genSExpr nid v

assignExprId :: SExpr () -> State CState (SExpr TypeVar)
assignExprId (IntLiteral _ v) = simpleAssignExprId IntLiteral v
assignExprId (FloatLiteral _ v) = simpleAssignExprId FloatLiteral v
assignExprId (SymbolLiteral _ v) = simpleAssignExprId SymbolLiteral v
assignExprId (StringLiteral _ v) = simpleAssignExprId StringLiteral v
assignExprId (Nil _) = simpleAssignExprId (\i _ -> Nil i) ()
assignExprId (Cons _ l r) = do
  lid <- assignExprId l
  rid <- assignExprId r
  nid <- cNextTypeVar
  return $ Cons nid lid rid

genConstraints sexpr = do
  defconstraints <- cAddDefaultConstraints
  isexpr <- assignExprId sexpr
  consts <- constraints isexpr
  let allconsts = defconstraints ++ consts in do 
    unify allconsts
    assignment <- cUnification
    showassignment <- mapM showpair assignment
    return $ (isexpr, allconsts, showassignment)
  where showpair (a, v, b) = do
                         b' <- pprintTypeMaybe unconstrainedVarString b
                         return $ "T" ++ (show a) ++ " = V" ++ (show v) ++ ":" ++ b'

walkAst :: (SExpr TypeVar -> IO ()) -> SExpr TypeVar -> IO ()
walkAst f x@(Cons _ l r) = do
  f x
  printf "\n"
  walkAst f l
  walkAst f r

walkAst f x = do
  f x
  printf "\n"

printAst :: SExpr TypeVar -> IO ()
printAst x = do
  printf "T%d = %s" (sexprdata x) (show x)

main = do
  putStrLn $ show isexpr
  putStrLn "-- AST:"
  walkAst printAst isexpr
  putStrLn "-- Constraints:"
  putStrLn $ intercalate "\n" $ map show constraints
  putStrLn "-- Unification:"
  putStrLn $ intercalate "\n" unif
  where (isexpr, constraints, unif) = case parseToplevel "(4)" of
                                        Left err -> error $ "No match: " ++ show err
                                        Right val -> evalState (genConstraints val) newstate

{-
main =
    putStrLn $ intercalate ", " $ map show sexprs
    putStrLn $ intercalate "\n" $ map constraints sexprs
    where sexprs = case parseToplevel "(a b c d e f g e h)" of
                     Left err -> error $ "No match: " ++ show err
                     Right val -> let monad = mapM assignExprId val :: State CState [(SExpr TypeVar)] in
                                  evalState monad newstate :: [SExpr TypeVar]

-}
