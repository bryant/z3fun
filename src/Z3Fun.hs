{-# LANGUAGE GADTs, KindSignatures, DataKinds, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

module Z3Fun where

import GHC.TypeLits (KnownNat, Nat, natVal)
import Control.Monad.Trans.State (State, get, modify, runState)
import Data.Word (Word64)
import Data.Proxy (Proxy(..))

data BitVec (n :: Nat)

data AST :: * -> * where
    Var :: Int -> AST a  -- variable id
    BitConst :: KnownNat n => Word64 -> AST (BitVec n)
    BoolConst :: Bool -> AST Bool
    BitBinOp :: KnownNat n => BitBinOp -> AST (BitVec n) -> AST (BitVec n)
             -> AST (BitVec n)
    BitUnOp :: KnownNat n => BitBinOp -> AST (BitVec n) -> AST (BitVec n)
    BitCmp :: KnownNat n => BitCmp -> AST (BitVec n) -> AST (BitVec n)
             -> AST Bool
    BoolBinOp :: BoolBinOp -> AST Bool -> AST Bool -> AST Bool
    BoolUnOp :: BoolUnOp -> AST Bool -> AST Bool
    Ite :: AST Bool -> AST t -> AST t -> AST t  -- if-then-else

data BitCmp
    = BitUlt
    | BitUgt
    | BitUle
    | BitUge
    | BitSlt
    | BitSgt
    | BitSle
    | BitSge
    | BitEq  -- equality

data BitBinOp
    = BitAdd
    | BitSub
    | BitMul
    | BitURem
    | BitSRem
    | BitSMod
    | BitShl
    | BitLShr
    | BitAShr
    | BitAnd
    | BitOr
    | BitXor
    | BitNor
    | BitNand

data BitUnOp = BitNeg | BitNot

data BoolBinOp
    = BoolAnd
    | BoolOr
    | BoolXor
    | BoolImp  -- ^ implication
    | BoolEq  -- ^ logical equivalence

data BoolUnOp = BoolNot

data Z3Env
    = Z3Env
    { preconditions :: [AST Bool]
    , var_id :: Int
    }

type Z3 = State Z3Env

next_var :: Z3 Int
next_var = var_id <$> get <* modify (\z -> z { var_id = var_id z + 1})

run_z3 :: Z3 a -> a
run_z3 = fst . flip runState (Z3Env [] 0)

word :: Z3 (AST (BitVec n))
word = Var <$> next_var

word8 :: Z3 (AST (BitVec 8))
word8 = word

word16 :: Z3 (AST (BitVec 16))
word16 = word

word32 :: Z3 (AST (BitVec 32))
word32 = word

word64 :: Z3 (AST (BitVec 64))
word64 = word

word128 :: Z3 (AST (BitVec 128))
word128 = word

class ToSMT t where to_smt :: t -> String

instance KnownNat n => ToSMT (AST (BitVec n)) where
    to_smt (Var n) = "x_" ++ show n
    to_smt (BitConst c)
        | nat_max < fromIntegral c = error msg
        | otherwise = terms ["_", "bv" ++ show c, show size]
        where
        size = fromIntegral $ natVal (Proxy :: Proxy n) :: Word64
        nat_max = 2 ^ (fromIntegral size :: Integer) - 1 :: Integer
        msg = "const " ++ show c ++ " is too large for BitVec " ++ show size
    to_smt (BitBinOp op lhs rhs) = term3 op lhs rhs
    to_smt (BitUnOp op t) = term2 op t
    to_smt (Ite cond t f) = terms ["ite", to_smt cond, to_smt t, to_smt f]

instance ToSMT (AST Bool) where
    to_smt (Var n) = "x_" ++ show n
    to_smt (BoolConst n) = if n then "true" else "false"
    to_smt (BitCmp cmp lhs rhs) = term3 cmp lhs rhs
    to_smt (BoolBinOp op lhs rhs) = term3 op lhs rhs
    to_smt (BoolUnOp op t) = term2 op t
    to_smt (Ite cond t f) = terms ["ite", to_smt cond, to_smt t, to_smt f]

instance ToSMT BitBinOp where
    to_smt BitAdd  = "bvadd"
    to_smt BitSub  = "bvsub"
    to_smt BitMul  = "bvmul"
    to_smt BitURem = "bvurem"
    to_smt BitSRem = "bvsrem"
    to_smt BitSMod = "bvsmod"
    to_smt BitShl  = "bvshl"
    to_smt BitLShr = "bvlshr"
    to_smt BitAShr = "bvashr"
    to_smt BitAnd  = "bvand"
    to_smt BitOr   = "bvor"
    to_smt BitXor  = "bvxor"
    to_smt BitNor  = "bvnor"
    to_smt BitNand = "bvnand"

instance ToSMT BitUnOp where
    to_smt BitNeg = "bvneg"
    to_smt BitNot = "bvnot"

instance ToSMT BoolUnOp where
    to_smt BoolNot = "not"

instance ToSMT BoolBinOp where
    to_smt BoolAnd = "and"
    to_smt BoolOr  = "or"
    to_smt BoolXor = "xor"
    to_smt BoolImp = "=>"
    to_smt BoolEq  = "="

instance ToSMT BitCmp where
    to_smt BitUlt = "bvult"
    to_smt BitUgt = "bvugt"
    to_smt BitUle = "bvule"
    to_smt BitUge = "bvuge"
    to_smt BitSlt = "bvslt"
    to_smt BitSgt = "bvsgt"
    to_smt BitSle = "bvsle"
    to_smt BitSge = "bvsge"
    to_smt BitEq  = "="

terms xs = "(" ++ unwords xs ++ ")"

term2 :: (ToSMT a, ToSMT b) => a -> b -> String
term2 a b = terms [to_smt a, to_smt b]

term3 :: (ToSMT a, ToSMT b, ToSMT c) => a -> b -> c -> String
term3 a b c = terms [to_smt a, to_smt b, to_smt c]

{-
main = do
    prove f
    where
    f x c0 c1 = c0 > 0 && x == (x << c0) >> c0 ==>
                (x << c0) > c1 <==> x > (c1 >> c0)
        where (>) = ugt
-}
