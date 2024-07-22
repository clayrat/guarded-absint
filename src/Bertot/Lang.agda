module Bertot.Lang where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

{- The programming language -}

data AExpr : 𝒰 where
  ANum  : ℕ → AExpr
  AVar  : String → AExpr
  APlus : AExpr → AExpr → AExpr

data BExpr : 𝒰 where
  BLt : AExpr → AExpr → BExpr

data Instr : 𝒰 where
  Skip   : Instr
  Assign : String → AExpr → Instr
  Seq    : Instr → Instr → Instr
  While  : BExpr → Instr → Instr

{- Weakest pre-condition calculus -}

data Assert : 𝒰 where
  QPred  : String → List AExpr → Assert
  QB     : BExpr → Assert
  QConj  : Assert → Assert → Assert
  QNot   : Assert → Assert
  QTrue  : Assert
  QFalse : Assert

{- Annotated instruction -}

data AnInstr : 𝒰 where
  AnPre    : Assert → AnInstr → AnInstr
  AnSkip   : AnInstr
  AnAssign : String → AExpr → AnInstr
  AnSeq    : AnInstr → AnInstr → AnInstr
  AnWhile  : BExpr → Assert → AnInstr → AnInstr

cleanup : AnInstr → Instr
cleanup (AnPre _ i)     = cleanup i
cleanup  AnSkip         = Skip
cleanup (AnAssign x e)  = Assign x e
cleanup (AnSeq i₁ i₂)   = Seq (cleanup i₁) (cleanup i₂)
cleanup (AnWhile b a i) = While b (cleanup i)
