{-# LANGUAGE GADTs, KindSignatures, DataKinds #-}

module Z3Fun where

import GHC.TypeLits (KnownNat, Nat)
import Control.Monad.Trans.State (State)

data BitVec (n :: Nat)

data AST :: * -> * where
    Var :: Int -> AST a  -- variable id
    BitConst :: KnownNat n => Integer -> AST (BitVec n)
    BoolConst :: Bool -> AST Bool
    BitBinOp :: KnownNat n => BitBinOp -> AST (BitVec n) -> AST (BitVec n)
             -> AST (BitVec n)
    BitUnOp :: KnownNat n => BitBinOp -> AST (BitVec n) -> AST (BitVec n)
    BitCmp :: KnownNat n => BitCmp -> AST (BitVec n) -> AST (BitVec n)
             -> AST Bool
    BoolBinOp :: BoolBinOp -> AST Bool -> AST Bool -> AST Bool
    BoolUnOp :: BoolUnOp -> AST Bool -> AST Bool
    TernOp :: AST Bool -> AST t -> AST t -> AST t

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

data BitUnOp = BitNeg | BitNot

data BoolBinOp
    = BoolAnd
    | BoolOr
    | BoolXor
    | BoolImp  -- ^ implication
    | BoolEq  -- ^ logical equivalence

data BoolUnOp = BoolNot

data Z3Env = Z3Env { var_id :: Int }

{-
main = do
    prove f
    where
    f x c0 c1 = c0 > 0 && x == (x << c0) >> c0 ==>
                (x << c0) > c1 <==> x > (c1 >> c0)
        where (>) = ugt
-}
