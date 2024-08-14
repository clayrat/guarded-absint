module Nipkow.OpSem where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

open import Nipkow.Lang
open import Nipkow.State as S

open S.State ℕ 0

{- Big-step operational semantics -}

{-
data SUpdate : State → String → ℕ → State → 𝒰 where
  SUp1 : ∀ {r x v v'} → SUpdate ((x , v) ∷ r) x v' ((x , v') ∷ r)
  SUp2 : ∀ {r r' x y v v'}
       → SUpdate r x v' r' → x ≠ y → SUpdate ((y , v) ∷ r) x v' ((y , v) ∷ r')

supd : ∀ {s x n s'}
     → SUpdate s x n s'
     → s' ＝ stupd x n s
supd .{s = (x , v) ∷ r} .{x = x} {n} .{s' = (x , v') ∷ r} (SUp1 {r} {x} {v} {v'})                =
  discrete-eq {x = x} {C = λ q → (x , n) ∷ r ＝ (if ⌊ q ⌋ then (x , n) ∷ r else (x , v) ∷ stupd x n r)}
    refl refl
supd .{s = (y , v) ∷ r} .{x = x} {n} .{s' = (y , v) ∷ r'} (SUp2 {r} {r'} {x} {y} {v} {v'} su ne) =
  discrete-ne {x = x} {C = λ q → (y , v) ∷ r' ＝ (if ⌊ q ⌋ then (y , n) ∷ r else (y , v) ∷ stupd x n r)}
    ne (ap ((y , v) ∷_) (supd su))
-}

data Exec : Instr → State → State → 𝒰 where
  ExSkip   : ∀ {s} → Exec Skip s s
  ExAssign : ∀ {x e s s'}
           -- → SUpdate s x (aval s e) s'
           → stupd x (aval s e) s ＝ s'
           → Exec (Assign x e) s s'
  ExSeq    : ∀ {s s' s'' i₁ i₂}
           → Exec i₁ s s' → Exec i₂ s' s'' → Exec (Seq i₁ i₂) s s''
  ExITET : ∀ {s s' b i₁ i₂}
           → is-true (bval s b)
           → Exec i₁ s s' → Exec (ITE b i₁ i₂) s s'
  ExITEF : ∀ {s s' b i₁ i₂}
           → is-true (not (bval s b))
           → Exec i₂ s s' → Exec (ITE b i₁ i₂) s s'
  ExWhileT : ∀ {s s' s'' b i}
           → is-true (bval s b)
           → Exec i s s' → Exec (While b i) s' s'' → Exec (While b i) s s''
  ExWhileF : ∀ {s b i}
           → is-true (not (bval s b)) → Exec (While b i) s s

{-
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
-}
