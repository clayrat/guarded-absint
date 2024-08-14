module Nipkow.CollSem where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.String
open import Data.List
open import Data.List.Correspondences.Binary.All
open import Data.Reflects

open import Combinatorics.Power
open import Order.Base
open import Order.Diagram.Lub
open import Order.SupLattice
open import Order.SupLattice.SmallBasis
open import Order.Constructions.Subsets

open import List1
open import Nipkow.Lang
open import Nipkow.OpSem
open import Nipkow.ACom
open import Nipkow.ACom.Leq
open import Nipkow.ACom.Order
open import Nipkow.State as S

module CollsemA
  (A : 𝒰 (ℓsuc 0ℓ))
  (sup : A → A → A)
  (leq : A → A → 𝒰)
  (leq-sup-r1 : ∀ {x a b} → leq x a → leq x (sup a b))
  (leq-sup-r2 : ∀ {x a b} → leq x b → leq x (sup a b))
  (leq-sup-l : ∀ {x a b} → leq a x → leq b x → leq (sup a b) x)
  where

  open List1.List1
  open AnInstrLeq A leq

  -- semantics

  stepA : (String → AExpr → A → A)
        → (BExpr → A → A)
        → A → AnInstr A → AnInstr A
  stepA f g s (AnSkip _)              = AnSkip s
  stepA f g s (AnAssign x e _)        = AnAssign x e (f x e s)
  stepA f g s (AnSeq c₁ c₂)           = AnSeq (stepA f g s c₁) (stepA f g (post c₁) c₂)
  stepA f g s (AnITE b p₁ c₁ p₂ c₂ q) = AnITE b (g b s) (stepA f g p₁ c₁) (g (BNot b) s) (stepA f g p₂ c₂) (sup (post c₁) (post c₂))
  stepA f g s (AnWhile inv b p c q)   = AnWhile (sup s (post c)) b (g b inv) (stepA f g p c) (g (BNot b) inv)

  strip-stepA : ∀ {f g s} c → strip (stepA f g s c) ＝ strip c
  strip-stepA (AnSkip _)            = refl
  strip-stepA (AnAssign x e _)      = refl
  strip-stepA (AnSeq c₁ c₂)         = ap² Seq (strip-stepA c₁) (strip-stepA c₂)
  strip-stepA (AnITE b _ c₁ _ c₂ _) = ap² (ITE b) (strip-stepA c₁) (strip-stepA c₂)
  strip-stepA (AnWhile inv b _ c _) = ap (While b) (strip-stepA c)

  mono2-stepA : ∀ {f : String → AExpr → A → A} {g : BExpr → A → A} {c₁ c₂}
              → (∀ {x e s₁ s₂} → leq s₁ s₂ → leq (f x e s₁) (f x e s₂))
              → (∀ {b s₁ s₂} → leq s₁ s₂ → leq (g b s₁) (g b s₂))
              → c₁ ≤ⁱ c₂
              → ∀ {s₁ s₂} → leq s₁ s₂ → stepA f g s₁ c₁ ≤ⁱ stepA f g s₂ c₂
  mono2-stepA {f} {g} {c₁ = AnSkip p}              {c₂} fm gm lc {s₁} {s₂} ls =
    let (s' , eq , _) = skip-≤ⁱ-eliml {c = c₂} lc in
    skip-≤ⁱ-intro2 refl (ap (stepA f g s₂) eq) ls
  mono2-stepA {f} {g} {c₁ = AnAssign x e p}        {c₂} fm gm lc {s₁} {s₂} ls =
    let (s' , eq , _) = assign-≤ⁱ-eliml {c = c₂} lc in
    assign-≤ⁱ-intro2 refl (ap (stepA f g s₂) eq) (fm ls)
  mono2-stepA {f} {g} {c₁ = AnSeq c₁ c₃}           {c₂} fm gm lc {s₁} {s₂} ls =
    let (a₁ , a₂ , eq , le₁ , le₂) = seq-≤ⁱ-eliml {c = c₂} lc in
    seq-≤ⁱ-intro2 refl (ap (stepA f g s₂) eq)
                  (mono2-stepA fm gm le₁ ls)
                  (mono2-stepA fm gm le₂ (mono-post le₁))
  mono2-stepA {f} {g} {c₁ = AnITE b p₁ c₁ p₂ c₃ q} {c₂} fm gm lc {s₁} {s₂} ls =
    let (p₃ , a₁ , p₄ , a₂ , q₂ , eq , le₁ , le₂ , le₃ , le₄ , _) = ite-≤ⁱ-eliml {c = c₂} lc in
    ite-≤ⁱ-intro2 refl (ap (stepA f g s₂) eq)
                  (gm ls) (mono2-stepA fm gm le₂ le₁)
                  (gm ls) (mono2-stepA fm gm le₄ le₃)
                  (leq-sup-l (leq-sup-r1 (mono-post {c₁ = c₁} le₂))
                             (leq-sup-r2 (mono-post {c₁ = c₃} le₄)))
  mono2-stepA {f} {g} {c₁ = AnWhile inv₁ b p c₁ q} {c₂} fm gm lc {s₁} {s₂} ls =
    let (inv₂ , p₂ , c₀ , q₂ , eq , le₁ , le₂ , le₃ , _) = while-≤ⁱ-eliml {c = c₂} lc in
    while-≤ⁱ-intro2 refl (ap (stepA f g s₂) eq)
                    (leq-sup-l (leq-sup-r1 ls) (leq-sup-r2 (mono-post le₃))) (gm le₁)
                    (mono2-stepA fm gm le₃ le₂) (gm le₁)

open S.State ℕ 0

SetState : 𝒰 (ℓsuc 0ℓ)
SetState = ℙ State 0ℓ

open AnInstrLeq SetState _⊆_
open CollsemA SetState _∪_ _⊆_
                        (λ {x} {a} {b} → ℙ-inl {A = a} {B = b} {C = x})
                        (λ {x} {a} {b} → ℙ-inr {A = a} {B = b} {C = x})
                        (λ {x} {a} {b} → ∪-⊆  {A = a} {B = b} {C = x})

-- TODO: AnInstr SetState ⇒ AnInstr SetState ?

step : SetState → AnInstr SetState → AnInstr SetState
step = stepA (λ x e → ℙ-map (λ s → stupd x (aval s e) s) .hom)
              λ b S s → el! (is-true (bval s b) × s ∈ S)

mono2-step : ∀ {c₁ c₂}
           → c₁ ≤ⁱ c₂
           → ∀ {s₁ s₂} → s₁ ⊆ s₂ → step s₁ c₁ ≤ⁱ step s₂ c₂
mono2-step =
  mono2-stepA (λ le → map (second (second le)))
              (λ le → second le)

strip-step : ∀ {s} {c} → strip (step s c) ＝ strip c
strip-step {c} = strip-stepA c

{- Relation to big-step semantics -}
big-step-post-step : ∀ {s s' i a ss}
                   → Exec i s s'
                   → strip a ＝ i
                   → s ∈ ss
                   → step ss a ≤ⁱ a
                   → s' ∈ post a
big-step-post-step {s} .{s' = s}    .{i = Skip}        {a} {ss}  ExSkip                                 seq sin stleq =
  let (p , eq) = strip-skip-r seq
      le = skip-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
   in
  subst (λ q → s ∈ post q) (eq ⁻¹) (le sin)
big-step-post-step {s}  {s'}        .{i = Assign x e}  {a} {ss} (ExAssign {x} {e} upd)                  seq sin stleq =
  let (p , eq) = strip-assign-r seq
      le = assign-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) (le ∣ (s , upd , sin) ∣₁)
big-step-post-step {s}  {s'}        .{i = Seq i₁ i₂}   {a} {ss} (ExSeq {i₁} {i₂} ex₁ ex₂)               seq sin stleq =
  let (a₁ , a₂ , eq , eq₁ , eq₂) = strip-seq-r seq
      (le1 , le2) = seq-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  big-step-post-step {a = a₂} {ss = post a₁} ex₂ eq₂
    (big-step-post-step {a = a₁} ex₁ eq₁ sin le1)
    le2
big-step-post-step {s}  {s'}        .{i = ITE b i₁ i₂} {a} {ss} (ExITET {b} {i₁} {i₂} bt ex)            seq sin stleq =
  let (p₁ , a₁ , p₂ , a₂ , q , eq , eq₁ , eq₂) = strip-ite-r seq
      (le1 , le2 , _ , _ , le5) = ite-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  le5 $
  ∣ inl (big-step-post-step {a = a₁} {ss = p₁} ex eq₁ (le1 (bt , sin)) le2) ∣₁
big-step-post-step {s}  {s'}        .{i = ITE b i₁ i₂} {a} {ss} (ExITEF {b} {i₁} {i₂} bf ex)            seq sin stleq =
  let (p₁ , a₁ , p₂ , a₂ , q , eq , eq₁ , eq₂) = strip-ite-r seq
      (_ , _ , le3 , le4 , le5) = ite-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  le5 $
  ∣ inr (big-step-post-step {a = a₂} {ss = p₂} ex eq₂ (le3 (bf , sin)) le4) ∣₁
big-step-post-step {s}  .{s' = s''} .{i = While b i}  {a} {ss} (ExWhileT {s'} {s''} {b} {i} bt ex₁ ex₂) seq sin stleq =
  let (inv , p , a₀ , q , eq , eq₁) = strip-while-r seq
      (le1 , le2 , le3 , le4) = while-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
    in
  subst (λ q → s'' ∈ post q) (eq ⁻¹) $
  big-step-post-step {s' = s''} {a = AnWhile inv b p a₀ q} {ss = post a₀} ex₂ (ap (While b) eq₁)
    (big-step-post-step {s' = s'} {a = a₀} {ss = p} ex₁ eq₁ (le2 (bt , le1 ∣ inl sin ∣₁)) le3)
    (While-≤ⁱ (le1 ∘ map [ inr , inr ]ᵤ) refl le2 le3 le4)
big-step-post-step {s}  {s'}        .{i = While b i}  {a} {ss} (ExWhileF {b} {i} bf)                    seq sin stleq =
  let (inv , p , a₀ , q , eq , eq₁) = strip-while-r seq
      (le1 , _ , _ , le4) = while-≤ⁱ-elim2 (ap (step ss) eq) eq stleq
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  le4 $
  bf , (le1 ∣ inl sin ∣₁)
