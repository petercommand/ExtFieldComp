--

{-# LANGUAGE DeriveFunctor, FlexibleInstances, TypeSynonymInstances #-}

import Control.Monad.State

-- Expressions of type a

data Expr a =   Ind
              | Lit a
              | Add (Expr a) (Expr a)
              | Sub (Expr a) (Expr a)
              | Mul (Expr a) (Expr a) deriving Functor

instance Eq a => Eq (Expr a) where
  Ind == Ind = True
  (Lit x) == (Lit y) = x == y
  (Add e1 e2) == (Add e1' e2') = (e1 == e1') && (e2 == e2')
  (Sub e1 e2) == (Sub e1' e2') = (e1 == e1') && (e2 == e2')
  (Mul e1 e2) == (Mul e1' e2') = (e1 == e1') && (e2 == e2')
  _ == _ = False

instance Show a => Show (Expr a) where
  show Ind = "X"
  show (Lit x) = show x ++ "'"
  show (Add e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
  show (Sub e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++ ")"
  show (Mul e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++ ")"

instance Num a => Num (Expr a) where
  fromInteger n = Lit $ fromInteger n
  e1 + e2 = Add e1 e2
  e1 - e2 = Sub e1 e2
  e1 * e2 = Mul e1 e2

foldExpr :: Num b => b -> (a -> b) -> Expr a -> b
foldExpr x _ Ind = x
foldExpr _ f (Lit x) = f x
foldExpr x f (Add e1 e2) = foldExpr x f e1 + foldExpr x f e2
foldExpr x f (Sub e1 e2) = foldExpr x f e1 - foldExpr x f e2
foldExpr x f (Mul e1 e2) = foldExpr x f e1 * foldExpr x f e2

type Expr2 a = Expr (Expr a)
type Expr3 a = Expr2 (Expr a)
type Expr4 a = Expr3 (Expr a)
type Expr5 a = Expr4 (Expr a)
type Expr6 a = Expr5 (Expr a)
-- ...

-- The semantics of an expression of type a

instance Num a => Num (a -> a) where
  fromInteger = const . fromInteger
  f + g = \x -> f x + g x
  f - g = \x -> f x - g x
  f * g = \x -> f x * g x

semantics :: Num a => Expr a -> a -> a
semantics = foldExpr id const

semantics2 :: Num a => Expr2 a -> Expr a -> a -> a
semantics2 e = semantics . semantics e

semantics3 :: Num a => Expr3 a -> Expr2 a -> Expr a -> a -> a
semantics3 e = semantics2 . semantics e

semantics4 :: Num a => Expr4 a -> Expr3 a -> Expr2 a -> Expr a -> a -> a
semantics4 e = semantics3 . semantics e
-- ...

-- Rotation (to the right) of indeterminates

idExpr2 :: Num a => Expr2 a -> Expr2 a
idExpr2 = foldExpr Ind (foldExpr (Lit Ind) (Lit . Lit))

rotrExpr2 :: Num a => Expr2 a -> Expr2 a
rotrExpr2 = foldExpr (Lit Ind) (foldExpr Ind (Lit . Lit))

rotrExpr3 :: Num a => Expr3 a -> Expr3 a
rotrExpr3 = (fmap $ rotrExpr2) . rotrExpr2

rotrExpr4 :: Num a => Expr4 a -> Expr4 a
rotrExpr4 = (fmap . fmap $ rotrExpr2) . rotrExpr3

rotrExpr5 :: Num a => Expr5 a -> Expr5 a
rotrExpr5 = (fmap . fmap . fmap $ rotrExpr2) . rotrExpr4

rotrExpr6 :: Num a => Expr6 a -> Expr6 a
rotrExpr6 = (fmap . fmap . fmap . fmap $ rotrExpr2) . rotrExpr5
-- ...

-- Symbolic substitution via semantics function

substitute :: Num a => Expr a -> Expr a -> Expr a
substitute e' e = semantics (rotrExpr2 $ Lit e) e'

substitute2 :: Num a => Expr2 a -> Expr2 a -> Expr2 a -> Expr2 a
substitute2 e1 e2 e = semantics2 (rotrExpr4 . rotrExpr4 $ Lit . Lit $ e) (Lit e1) e2

substitute3 :: Num a => Expr3 a -> Expr3 a -> Expr3 a -> Expr3 a -> Expr3 a
substitute3 e1 e2 e3 e = semantics3 (rotrExpr6 . rotrExpr6 . rotrExpr6 $ Lit . Lit . Lit $ e) (Lit . Lit $ e1) (Lit e2) e3
-- ...

-- Symbols of type a

data Sym a = Var Integer deriving Show

-- SSA statements of type a

type SSA a = State (Sym a, [String]) (Sym a)

instance Show (SSA a) where
  show s = unlines . snd $ execState s (Var 0, [])

getvar :: SSA a
getvar = state $ \(Var n, is) -> (Var n, (Var (n + 1), is))

putins :: String -> SSA a
putins i = state $ \(s, is) -> (s, (s, is ++ [i]))

gen_assign :: Show a => Sym a -> a -> String
gen_assign dst val = show dst ++ " := " ++ show val

gen_ind :: Show a => Sym a -> Integer -> String
gen_ind dst ind = show dst ++ " := Ind " ++ show ind

gen_arith :: Show a => String -> Sym a -> Sym a -> Sym a -> String
gen_arith op dst src1 src2 = show dst ++ " := " ++ show src1 ++ op ++ show src2

instance Show a => Num (SSA a) where
  p1 + p2 = do x <- p1
               y <- p2
               z <- getvar
               putins $ gen_arith " + " z x y
               return z
  p1 - p2 = do x <- p1
               y <- p2
               z <- getvar
               putins $ gen_arith " - " z x y
               return z
  p1 * p2 = do x <- p1
               y <- p2
               z <- getvar
               putins $ gen_arith " * " z x y
               return z

-- Compiling expressions of type a to SSA statements

pass :: SSA a
pass = do { v <- getvar ; return v }

compile0 :: Show a => a -> SSA a
compile0 x = do { v <- getvar ; putins $ gen_assign v x ; return v }

compile :: Show a => Expr a -> SSA a
compile = foldExpr pass compile0

compile2 :: Show a => Expr2 a -> SSA a
compile2 = foldExpr pass compile

compile3 :: Show a => Expr3 a -> SSA a
compile3 = foldExpr pass compile2

compile4 :: Show a => Expr4 a -> SSA a
compile4 = foldExpr pass compile3
-- ...

-- Test cases for evaluating and compiling expressions of Float

x = Ind :: Expr Float
e1 = 1 + 2*x
s1 = semantics e1
v1 = s1 3
p1 = compile e1
e2 = substitute e1 (4 + 5*x)
s2 = semantics e2
v2 = s2 6
p2 = compile e2
y = Ind :: Expr2 Float
z = Ind :: Expr3 Float
e3 = (z + 1)*(Lit y + 2)*((Lit . Lit $ x) + 3)
s3 = semantics3 e3
v3 = s3 4 5 6
p3 = compile3 e3
e3' = rotrExpr3 e3
e3'' = rotrExpr3 e3'
e3''' = rotrExpr3 e3''
e4 = Lit e3 + Ind :: Expr4 Float
e4' = rotrExpr4 . rotrExpr4 . rotrExpr4 . rotrExpr4 $ e4
e5 = (1 + Lit x)*(2 + y)
e6 = (3 + Lit x)*(4 + y*y)
e7 = (5 + Lit x)*(6 + y*(7 + y))
e7' = substitute2 e5 e6 e7

-- Types that are extended from other types

class Extended f where
  fromList :: [a] -> f a
  toList :: f a -> [a]

-- Expanding an expression of an extended type

expand2 :: (Extended f, Functor f, Num a, Num (f (Expr2 a))) => Expr (f a) -> f (Expr2 a)
expand2 = foldExpr (fromList [Ind, Lit Ind]) (fmap $ Lit . Lit)

expand3 :: (Extended f, Functor f, Num a, Num (f (Expr3 a))) => Expr (f a) -> f (Expr3 a)
expand3 = foldExpr (fromList [Ind, Lit Ind, Lit . Lit $ Ind]) (fmap $ Lit . Lit . Lit)

expand24 :: (Extended f, Functor f, Num a, Num (f (Expr2 a)), Num (f (Expr4 a))) => Expr2 (f a) -> f (Expr4 a)
expand24 = expand2 . fmap expand2

expand26 :: (Extended f, Functor f, Num a, Num (f (Expr3 a)), Num (f (Expr6 a))) => Expr2 (f a) -> f (Expr6 a)
expand26 = expand3 . fmap expand3

expand36 :: (Extended f, Functor f, Num a, Num (f (Expr2 a)), Num (f (Expr4 a)), Num (f (Expr6 a))) => Expr3 (f a) -> f (Expr6 a)
expand36 = expand2 . (fmap expand2) . (fmap . fmap $ expand2)

-- ...

-- Test cases for expanding and compiling expressions of extended types

-- The Gaussian numbers

data MyGaussian a = Complex a a deriving Functor

instance Show a => Show (MyGaussian a) where
  show (Complex a b) = "(" ++ show a ++ " + " ++ "i" ++ show b ++ ")"

instance Num a => Num (MyGaussian a) where
  fromInteger n = Complex (fromInteger n) 0
  Complex a1 b1 + Complex a2 b2 = Complex (a1 + a2) (b1 + b2)
  Complex a1 b1 - Complex a2 b2 = Complex (a1 - a2) (b1 - b2)
  Complex a1 b1 * Complex a2 b2 = Complex (a1*a2 - b1*b2) (a1*b2 + a2*b1)

instance Extended MyGaussian where
  fromList [x, y] = Complex x y
  toList (Complex x y) = [x, y]

-- The rational numbers

data MyRational a = Rational a a deriving Functor

instance Show a => Show (MyRational a) where
  show (Rational a b) = "(" ++ show a ++ "/" ++ show b ++ ")"

instance Num a => Num (MyRational a) where
  fromInteger n = Rational (fromInteger n) 1
  Rational a1 b1 + Rational a2 b2 = Rational (a1*b2 + a2*b1) (b1*b2)
  Rational a1 b1 - Rational a2 b2 = Rational (a1*b2 - a2*b1) (b1*b2)
  Rational a1 b1 * Rational a2 b2 = Rational (a1*a2) (b1*b2)

instance Extended MyRational where
  fromList [x, y] = Rational x y
  toList (Rational x y) = [x, y]

-- Compiling (MyGaussian (MyRational a)) to a

compileGR :: (Num a, Show a) => Expr (MyGaussian (MyRational a)) -> [SSA a]
compileGR = map compile4 . concat. map toList . map expand24 . toList . expand2

-- Test cases for compiling expressions of extended types

e8 = Ind + Lit (Complex (Rational 1 2) (Rational 3 4)) * Lit (Complex (Rational 5 6) (Rational 7 8))
p8 = compileGR e8

