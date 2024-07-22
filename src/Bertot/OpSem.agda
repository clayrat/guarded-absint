module Bertot.OpSem where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

open import Bertot.Lang

{- Big-step operational semantics -}

Env : 𝒰
Env = List (String × ℕ)

e→f : Env → (String → ℕ) → String → ℕ
e→f []            g   = g
e→f ((s , n) ∷ r) g v = if ⌊ s ≟ v ⌋ then n else e→f r g v

data AEval : Env → AExpr → ℕ → 𝒰 where
  AEN    : ∀ {r n} → AEval r (ANum n) n
  AEVar1 : ∀ {r x v} → AEval ((x , v) ∷ r) (AVar x) v
  AEVar2 : ∀ {r x y v v'}
         → x ≠ y → AEval r (AVar x) v' → AEval ((y , v) ∷ r) (AVar x) v'
  AEPlus : ∀ {r e1 e2 v1 v2}
         → AEval r e1 v1 → AEval r e2 v2 → AEval r (APlus e1 e2) (v1 + v2)

data BEval : Env → BExpr → Bool → 𝒰 where
  BELtT : ∀ {r e1 e2 v1 v2}
        → AEval r e1 v1 → AEval r e2 v2
        → v1 < v2 → BEval r (BLt e1 e2) true
  BELtF : ∀ {r e1 e2 v1 v2}
        → AEval r e1 v1 → AEval r e2 v2
        → v2 ≤ v1 → BEval r (BLt e1 e2) false

data SUpdate : Env → String → ℕ → Env → 𝒰 where
  SUp1 : ∀ {r x v v'} → SUpdate ((x , v) ∷ r) x v' ((x , v') ∷ r)
  SUp2 : ∀ {r r' x y v v'}
       → SUpdate r x v' r' → x ≠ y → SUpdate ((y , v) ∷ r) x v' ((y , v) ∷ r')

data Exec : Env → Instr → Env → 𝒰 where
  ExSkip   : ∀ {r} → Exec r Skip r
  ExAssign : ∀ {r r' x e v}
           → AEval r e v → SUpdate r x v r' → Exec r (Assign x e) r'
  ExSeq    : ∀ {r r' r'' i1 i2}
           → Exec r i1 r' → Exec r' i2 r'' → Exec r (Seq i1 i2) r''
  ExWhileT : ∀ {r r' r'' b i}
           → BEval r b true
           → Exec r i r' → Exec r' (While b i) r'' → Exec r (While b i) r''
  ExWhileF : ∀ {r b i}
           → BEval r b false → Exec r (While b i) r
