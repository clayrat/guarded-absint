module Absint where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Lang

module AInt
  (A : 𝒰)
  (fromN : ℕ → A)
  (top : A)
  (add : A → A → A)
  (to-pred : A → AExpr → Assert)
  (m : String → List ℕ → 𝒰) {- TODO prop ? -}
  (top-sem : ∀ e → to-pred top e ＝ QTrue)
  (to-pred-sem : ∀ g v e → ia m g (to-pred v e) ＝ ia m g (to-pred v (ANum (af g e))))
  (subst-to-pred : ∀ v x e e' → xsubst x e' (to-pred v e) ＝ to-pred v (asubst x e' e))
  (fromN-sem : ∀ g x → ia m g (to-pred (fromN x) (ANum x)))
  (a-add-sem : ∀ g v1 v2 x1 x2
            → ia m g (to-pred v1 (ANum x1)) → ia m g (to-pred v2 (ANum x2))
            → ia m g (to-pred (add v1 v2) (ANum (x1 + x2))))
  where            

  State : 𝒰
  State = List (String × A)

  lup : State → String → A
  lup []            x = top
  lup ((y , v) ∷ t) x = if x =ₛ y then v else lup t x

  a-upd : String → A → State → State
  a-upd x v []            = (x , v) ∷ [] 
  a-upd x v ((y , w) ∷ t) = if x =ₛ y then (y , v) ∷ t else (y , w) ∷ a-upd x v t

  a-af : State → AExpr → A
  a-af s (ANum n)      = fromN n
  a-af s (AVar x)      = lup s x
  a-af s (APlus e₁ e₂) = add (a-af s e₁) (a-af s e₂)

  s→a : State → Assert
  s→a []            = QTrue
  s→a ((x , a) ∷ t) = QConj (to-pred a (AVar x)) (s→a t)

  ab1 : Instr → State → AnInstr × State
  ab1 (Assign x e) s =
    (AnPre (s→a s) (AnAssign x e)) , a-upd x (a-af s e) s
  ab1 (Seq i₁ i₂)  s =
    let (ai₁ , s₁) = ab1 i₁ s 
        (ai₂ , s₂) = ab1 i₂ s₁ 
     in 
    AnSeq ai₁ ai₂ , s₂
  ab1 (While b i)  s =
    let (ai , _) = ab1 i [] in 
    AnWhile b (s→a []) ai , []

  mem : String → List String → Bool
  mem s []      = false
  mem s (x ∷ l) = (x =ₛ s) or mem s l

  no-dups : State → List String → Bool
  no-dups []            l = true
  no-dups ((s , _) ∷ t) l = not (mem s l) and no-dups t (s ∷ l)

  consistent : State → 𝒰
  consistent s = is-true (no-dups s [])

  consistent-prop : (s : State) → is-prop (consistent s)
  consistent-prop s = hlevel 1

  consistent-nil : consistent []
  consistent-nil = tt
