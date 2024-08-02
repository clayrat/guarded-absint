module Nipkow.CollSem where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming (elim to elimᵇ)
open import Data.Nat
--open import Data.Nat.Order.Inductive
open import Data.Sum
open import Data.String
open import Data.List
open import Data.List.Correspondences.Binary.All2
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects renaming (dmap to dmapʳ)

open import Order.Base
open import Combinatorics.Power

open import List1
open import Nipkow.Lang
open import Nipkow.OpSem
open import Nipkow.ACom
open import Nipkow.State as S

module AnInstrLeq
  (A : 𝒰 (ℓsuc 0ℓ))
  (leq : A → A → 𝒰)
  where

  open List1.List1

  _≤ⁱ_ : AnInstr A → AnInstr A → 𝒰 (ℓsuc 0ℓ)
  c₁ ≤ⁱ c₂ = (strip c₁ ＝ strip c₂) × All2₁ leq (annos c₁) (annos c₂)

  opaque
    skip-≤ⁱ-l : ∀ {s c}
              → (s' : A) → c ＝ AnSkip s' → leq s s'
              → AnSkip s ≤ⁱ c
    skip-≤ⁱ-l {s} s' eq le = subst (AnSkip s ≤ⁱ_) (eq ⁻¹) (refl , ([] , le))

    skip-≤ⁱ-r : ∀ {s c}
              → AnSkip s ≤ⁱ c
              → Σ[ s' ꞉ A ] (c ＝ AnSkip s') × leq s s'
    skip-≤ⁱ-r {s} {c} (h1 , h2 , h3) =
      let (s' , eq) = strip-skip-r (h1 ⁻¹) in
      s' , eq , subst (leq s) (ap post eq) h3

    skip-≤ⁱ-r-id : ∀ {s s'}
                 → AnSkip s ≤ⁱ AnSkip s'
                 → leq s s'
    skip-≤ⁱ-r-id {s} {s'} (h1 , h2 , h3) = h3

    assign-≤ⁱ-l : ∀ {x e s c}
                → (s' : A) → c ＝ AnAssign x e s' → leq s s'
                → AnAssign x e s ≤ⁱ c
    assign-≤ⁱ-l {x} {e} {s} s' eq le =
      subst (AnAssign x e s ≤ⁱ_) (eq ⁻¹) (refl , ([] , le))

    assign-≤ⁱ-r : ∀ {x e s c}
                → AnAssign x e s ≤ⁱ c
                → Σ[ s' ꞉ A ] (c ＝ AnAssign x e s') × leq s s'
    assign-≤ⁱ-r {x} {e} {s} {c} (h1 , h2 , h3) =
      let (s' , eq) = strip-assign-r (h1 ⁻¹) in
      s' , eq , subst (leq s) (ap post eq) h3

    assign-≤ⁱ-r-id : ∀ {x e s s'}
                   → AnAssign x e s ≤ⁱ AnAssign x e s'
                   → leq s s'
    assign-≤ⁱ-r-id {x} {e} {s} {s'} (h1 , h2 , h3) = h3

    seq-≤ⁱ-l : ∀ {c₁ c₂ c}
             → (c₃ c₄ : AnInstr A) → c ＝ AnSeq c₃ c₄ → c₁ ≤ⁱ c₃ → c₂ ≤ⁱ c₄
             → AnSeq c₁ c₂ ≤ⁱ c
    seq-≤ⁱ-l {c₁} {c₂} c₃ c₄ eq le₁ le₂ =
      subst (AnSeq c₁ c₂ ≤ⁱ_) (eq ⁻¹)
        (ap² Seq (le₁ .fst) (le₂ .fst) , All2₁-++₁ (le₁ .snd) (le₂ .snd))

    seq-≤ⁱ-r : ∀ {c₁ c₂ c}
             → AnSeq c₁ c₂ ≤ⁱ c
             → Σ[ c₃ ꞉ AnInstr A ] Σ[ c₄ ꞉ AnInstr A ]
                 (c ＝ AnSeq c₃ c₄) × c₁ ≤ⁱ c₃ × c₂ ≤ⁱ c₄
    seq-≤ⁱ-r {c₁} {c₂} {c} (h1 , h2) =
      let (a₁ , a₂ , eq₁ , eq₂ , eq₃) = strip-seq-r (h1 ⁻¹)
          (le1 , le2) = All2₁-split
                          (length-annos-same {c₁ = c₁}
                             (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₂ ⁻¹)))
                          (subst (All2₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) eq₁ h2)
         in
        a₁ , a₂ , eq₁ , (eq₂ ⁻¹ , le1) , eq₃ ⁻¹ , le2

    seq-≤ⁱ-r-id : ∀ {c₁ c₂ c₃ c₄}
                → AnSeq c₁ c₂ ≤ⁱ AnSeq c₃ c₄
                → c₁ ≤ⁱ c₃ × c₂ ≤ⁱ c₄
    seq-≤ⁱ-r-id {c₁} {c₂} le =
      let (a₁ , a₂ , eq , le₁ , le₂) = seq-≤ⁱ-r le
          (eq₁ , eq₂) = AnSeq-inj eq
        in
      subst (c₁ ≤ⁱ_) (eq₁ ⁻¹) le₁ , subst (c₂ ≤ⁱ_) (eq₂ ⁻¹) le₂

    ite-≤ⁱ-l : ∀ {b p₁ c₁ p₂ c₂ q₁ c}
             → (p₃ : A) → (c₃ : AnInstr A) → (p₄ : A) → (c₄ : AnInstr A) → (q₂ : A)
             → c ＝ AnITE b p₃ c₃ p₄ c₄ q₂
             → leq p₁ p₃ → c₁ ≤ⁱ c₃ → leq p₂ p₄ → c₂ ≤ⁱ c₄ → leq q₁ q₂
             → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c
    ite-≤ⁱ-l {b} {p₁} {c₁} {p₂} {c₂} {q₁} p₃ c₃ p₄ c₄ q₂ eq le₁ le₂ le₃ le₄ le₅ =
      subst (AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ_) (eq ⁻¹)
        ( ap² (ITE b) (le₂ .fst) (le₄ .fst)
        , All2₁-∶+₁-r (All2₁-++₁ (All2-∶∶₁-r le₁ (le₂ .snd)) (All2-∶∶₁-r le₃ (le₄ .snd))) le₅)

    ite-≤ⁱ-r : ∀ {b p₁ c₁ p₂ c₂ q₁ c}
             → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c
             → Σ[ p₃ ꞉ A ] Σ[ c₃ ꞉ AnInstr A ] Σ[ p₄ ꞉ A ] Σ[ c₄ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                              (c ＝ AnITE b p₃ c₃ p₄ c₄ q₂)
                            × leq p₁ p₃ × c₁ ≤ⁱ c₃ × leq p₂ p₄ × c₂ ≤ⁱ c₄ × leq q₁ q₂
    ite-≤ⁱ-r {b} {p₁} {c₁} {p₂} {c₂} {q₁} {c} (h1 , h2) =
      let (p₃ , a₁ , p₄ , a₂ , q , eq , eq₁ , eq₂) = strip-ite-r (h1 ⁻¹)
          le = All2₁-∶+₁-l (  length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
                            ∙ ap² (λ x y → suc x + suc y)
                                  (length-annos-same {c₁ = c₁}
                                     (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₁ ⁻¹)))
                                  (length-annos-same {c₁ = c₂}
                                     (reflects-true (reflects-instr (strip c₂) (strip a₂)) (eq₂ ⁻¹)))
                            ∙ length₁-++ {xs = p₃ ∷₁ annos a₁} {ys = p₄ ∷₁ annos a₂} ⁻¹) $
                 subst (All2₁ leq (((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₁) ∘ annos) eq h2
          le1 = All2₁-split ((ap suc (length-annos-same {c₁ = c₁} (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₁ ⁻¹)))))
                             (le .fst)
          le2 = All2-∶∶₁-l (le1 .fst)
          le3 = All2-∶∶₁-l (le1 .snd)
        in
      p₃ , a₁ , p₄ , a₂ , q , eq , le2 .fst , (eq₁ ⁻¹ , le2 .snd) , le3 .fst , (eq₂ ⁻¹ , le3 .snd) , le .snd

    ite-≤ⁱ-r-id : ∀ {b p₁ c₁ p₂ c₂ q₁ p₃ c₃ p₄ c₄ q₂}
                → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ AnITE b p₃ c₃ p₄ c₄ q₂
                → leq p₁ p₃ × c₁ ≤ⁱ c₃ × leq p₂ p₄ × c₂ ≤ⁱ c₄ × leq q₁ q₂
    ite-≤ⁱ-r-id {b} {p₁} {c₁} {p₂} {c₂} {q₁} {p₃} {c₃} {p₄} {c₄} {q₂} le =
      let (r₁ , a₁ , r₂ , a₂ , w₁ , eq , le₁ , le₂ , le₃ , le₄ , le₅) = ite-≤ⁱ-r le
          (_ , eq₁ , eq₂ , eq₃ , eq₄ , eq₅) = AnITE-inj eq
        in
        subst (leq p₁) (eq₁ ⁻¹) le₁
      , subst (c₁ ≤ⁱ_) (eq₂ ⁻¹) le₂
      , subst (leq p₂) (eq₃ ⁻¹) le₃
      , subst (c₂ ≤ⁱ_) (eq₄ ⁻¹) le₄
      , subst (leq q₁) (eq₅ ⁻¹) le₅

    while-≤ⁱ-l : ∀ {inv₁ b p₁ c₁ q₁ c}
               → (inv₂ : A) (p₂ : A) (c₂ : AnInstr A) (q₂ : A)
               → c ＝ AnWhile inv₂ b p₂ c₂ q₂
               → leq inv₁ inv₂ → leq p₁ p₂
               → c₁ ≤ⁱ c₂ → leq q₁ q₂
               → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ c
    while-≤ⁱ-l {inv₁} {b} {p₁} {c₁} {q₁} {c} inv₂ p₂ c₂ q₂ eq le₁ le₂ le₃ le₄ =
      subst (AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ_) (eq ⁻¹)
        ( ap (While b) (le₃ .fst)
        , All2₁-∶+₁-r (All2-∶∶₁-r le₁ (All2-∶∶₁-r le₂ (le₃ .snd))) le₄)

    while-≤ⁱ-r : ∀ {inv₁ b p₁ c₁ q₁ c}
               → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ c
               → Σ[ inv₂ ꞉ A ] Σ[ p₂ ꞉ A ] Σ[ c₂ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                     (c ＝ AnWhile inv₂ b p₂ c₂ q₂)
                   × leq inv₁ inv₂ × leq p₁ p₂ × c₁ ≤ⁱ c₂ × leq q₁ q₂
    while-≤ⁱ-r {inv₁} {b} {p₁} {c₁} {q₁} {c} (h1 , h2) =
      let (inv₂ , p , a , q , eq , eq₁) = strip-while-r (h1 ⁻¹)
          le = All2₁-∶+₁-l (ap (2 +_)
                              (length-annos-same {c₁ = c₁}
                                (reflects-true (reflects-instr (strip c₁) (strip a)) (eq₁ ⁻¹)))) $
               subst (All2₁ leq (((inv₁ ∷₁ (p₁ ∷₁ annos c₁)) ∶+₁ q₁)) ∘ annos) eq h2
          le1 = All2-∶∶₁-l (le .fst)
          le2 = All2-∶∶₁-l (le1 .snd)
       in
      inv₂ , p , a , q , eq , le1 .fst , le2 .fst , (eq₁ ⁻¹ , le2 .snd) , le .snd

    while-≤ⁱ-r-id : ∀ {b inv₁ p₁ c₁ q₁ inv₂ p₂ c₂ q₂}
                  → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ AnWhile inv₂ b p₂ c₂ q₂
                  → leq inv₁ inv₂ × leq p₁ p₂ × c₁ ≤ⁱ c₂ × leq q₁ q₂
    while-≤ⁱ-r-id {b} {inv₁} {p₁} {c₁} {q₁} {inv₂} {p₂} {c₂} {q₂} le =
      let (inv₀ , p , a , q , eq , le1 , le2 , le3 , le4) = while-≤ⁱ-r le
          (eq₁ , _ , eq₂ , eq₃ , eq₄) = AnWhile-inj eq
        in
        subst (leq inv₁) (eq₁ ⁻¹) le1
      , subst (leq p₁) (eq₂ ⁻¹) le2
      , subst (c₁ ≤ⁱ_) (eq₃ ⁻¹) le3
      , subst (leq q₁) (eq₄ ⁻¹) le4

  mono-post : ∀ {c₁ c₂} → c₁ ≤ⁱ c₂ → leq (post c₁) (post c₂)
  mono-post (_ , _ , h) = h

module AnInstrOrd
  (P : Poset (ℓsuc 0ℓ) 0ℓ)
  where

  open Poset P
  open AnInstrLeq Ob _≤_

  an-poset : Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  an-poset .Poset.Ob                                = AnInstr ⌞ P ⌟
  an-poset .Poset._≤_                               = _≤ⁱ_
  an-poset .Poset.≤-thin                            = ×-is-of-hlevel 1 (instr-is-set (strip _) (strip _))
                                                                       (All2₁-is-of-hlevel 0 (λ _ _ → ≤-thin))
  an-poset .Poset.≤-refl                            = refl , all2₁-refl (λ _ → ≤-refl)
  an-poset .Poset.≤-trans (exy , axy) (eyz , ayz)   = exy ∙ eyz , all2₁-trans (λ _ _ _ → ≤-trans) axy ayz
  an-poset .Poset.≤-antisym (exy , axy) (eyx , ayx) =
    strip-annos-same (reflects-true (reflects-instr (strip _) (strip _)) exy)
                     (all2₁-antisym (λ _ _ → ≤-antisym) axy ayx)

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
    let (s' , eq , _) = skip-≤ⁱ-r {c = c₂} lc in
    skip-≤ⁱ-l {c = stepA f g s₂ c₂} s₂ (ap (stepA f g s₂) eq) ls
  mono2-stepA {f} {g} {c₁ = AnAssign x e p}        {c₂} fm gm lc {s₁} {s₂} ls =
    let (s' , eq , _) = assign-≤ⁱ-r {c = c₂} lc in
    assign-≤ⁱ-l {c = stepA f g s₂ c₂} (f x e s₂) (ap (stepA f g s₂) eq) (fm ls)
  mono2-stepA {f} {g} {c₁ = AnSeq c₁ c₃}           {c₂} fm gm lc {s₁} {s₂} ls =
    let (a₁ , a₂ , eq , le₁ , le₂) = seq-≤ⁱ-r {c = c₂} lc in
    seq-≤ⁱ-l {c = stepA f g s₂ c₂}
             (stepA f g s₂ a₁)
             (stepA f g (post a₁) a₂)
             (ap (stepA f g s₂) eq)
             (mono2-stepA fm gm le₁ ls)
             (mono2-stepA fm gm le₂ (mono-post le₁))
  mono2-stepA {f} {g} {c₁ = AnITE b p₁ c₁ p₂ c₃ q} {c₂} fm gm lc {s₁} {s₂} ls =
    let (p₃ , a₁ , p₄ , a₂ , q₂ , eq , le₁ , le₂ , le₃ , le₄ , _) = ite-≤ⁱ-r {c = c₂} lc in
    ite-≤ⁱ-l {c = stepA f g s₂ c₂}
             (g b s₂) (stepA f g p₃ a₁) (g (BNot b) s₂) (stepA f g p₄ a₂) (sup (post a₁) (post a₂))
             (ap (stepA f g s₂) eq)
             (gm ls) (mono2-stepA fm gm le₂ le₁)
             (gm ls) (mono2-stepA fm gm le₄ le₃)
             (leq-sup-l (leq-sup-r1 (mono-post {c₁ = c₁} le₂))
                        (leq-sup-r2 (mono-post {c₁ = c₃} le₄)))
  mono2-stepA {f} {g} {c₁ = AnWhile inv₁ b p c₁ q} {c₂} fm gm lc {s₁} {s₂} ls =
    let (inv₂ , p₂ , c₀ , q₂ , eq , le₁ , le₂ , le₃ , _) = while-≤ⁱ-r {c = c₂} lc in
    while-≤ⁱ-l {c = stepA f g s₂ c₂}
               (sup s₂ (post c₀)) (g b inv₂) (stepA f g p₂ c₀) (g (BNot b) inv₂)
               (ap (stepA f g s₂) eq)
               (leq-sup-l (leq-sup-r1 ls) (leq-sup-r2 (mono-post le₃))) (gm le₁)
               (mono2-stepA fm gm le₃ le₂) (gm le₁)

open S.State ℕ 0

SetState : 𝒰 (ℓsuc 0ℓ)
SetState = ℙ State 0ℓ

open AnInstrLeq SetState _⊆_
open CollsemA SetState _∪_ _⊆_
                        (λ {x} {a} {b} → ⊆-∪-r-l {A = a} {B = b} {C = x})
                        (λ {x} {a} {b} → ⊆-∪-r-r {A = a} {B = b} {C = x})
                        (λ {x} {a} {b} → ⊆-∪-l   {A = a} {B = b} {C = x})

step : SetState → AnInstr SetState → AnInstr SetState
step = stepA (λ x e → ℙ-map' (λ s → stupd x (aval s e) s))
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
                   → Exec i s s' → strip a ＝ i
                   → s ∈ ss
                   → step ss a ≤ⁱ a
                   → s' ∈ post a
big-step-post-step {s} .{s' = s}    .{i = Skip}        {a} {ss}  ExSkip                                 seq sin stleq =
  let (p , eq) = strip-skip-r seq
      le = skip-≤ⁱ-r-id {s = λ z → el! ⌞ z ∈ ss ⌟} {s' = λ z → el! ⌞ z ∈ strip-skip-r seq .fst ⌟} $
           subst (λ q → step ss q ≤ⁱ q) eq stleq
   in
  subst (λ q → s ∈ post q) (eq ⁻¹) (le sin)
big-step-post-step {s}  {s'}        .{i = Assign x e}  {a} {ss} (ExAssign {x} {e} upd)                  seq sin stleq =
  let (p , eq) = strip-assign-r seq
      le = assign-≤ⁱ-r-id {s = λ z → el! (∃[ w ꞉ State ] (z ＝ stupd x (aval w e) w) × (w ∈ ss))}
                          {s' = λ z → el! ⌞ z ∈ strip-assign-r seq .fst ⌟}
                          $
           subst (λ q → step ss q ≤ⁱ q) eq stleq
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) (le ∣ (s , upd , sin) ∣₁)
big-step-post-step {s}  {s'}        .{i = Seq i₁ i₂}   {a} {ss} (ExSeq {i₁} {i₂} ex₁ ex₂)               seq sin stleq =
  let (a₁ , a₂ , eq , eq₁ , eq₂) = strip-seq-r seq
      le12 = seq-≤ⁱ-r-id $ subst (λ q → step ss q ≤ⁱ q) eq stleq
      le1 = le12 .fst
      le2 = le12 .snd
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  big-step-post-step {a = a₂} {ss = post a₁}
    ex₂ eq₂ (big-step-post-step {a = a₁} ex₁ eq₁ sin le1) le2
big-step-post-step {s}  {s'}        .{i = ITE b i₁ i₂} {a} {ss} (ExITET {b} {i₁} {i₂} bt ex)            seq sin stleq =
  let (p₁ , a₁ , p₂ , a₂ , q , eq , eq₁ , eq₂) = strip-ite-r seq
      le12345 = ite-≤ⁱ-r-id {q₁ = λ z → el! ((z ∈ post a₁) ⊎₁ (z ∈ post a₂))}
                            {q₂ = λ z → el! ⌞ z ∈ strip-ite-r seq .snd .snd .snd .snd .fst ⌟} $
                subst (λ q → step ss q ≤ⁱ q) eq stleq
      le1 = le12345 .fst
      le2 = le12345 .snd .fst
      le5 = le12345 .snd .snd .snd .snd
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  le5 $
  ∣ inl (big-step-post-step {a = a₁} {ss = p₁} ex eq₁ (le1 (bt , sin)) le2) ∣₁
big-step-post-step {s}  {s'}        .{i = ITE b i₁ i₂} {a} {ss} (ExITEF {b} {i₁} {i₂} bf ex)            seq sin stleq =
  let (p₁ , a₁ , p₂ , a₂ , q , eq , eq₁ , eq₂) = strip-ite-r seq
      le12345 = ite-≤ⁱ-r-id {q₁ = λ z → el! ((z ∈ post a₁) ⊎₁ (z ∈ post a₂))}
                            {q₂ = λ z → el! ⌞ z ∈ strip-ite-r seq .snd .snd .snd .snd .fst ⌟} $
                subst (λ q → step ss q ≤ⁱ q) eq stleq
      le3 = le12345 .snd .snd .fst
      le4 = le12345 .snd .snd .snd .fst
      le5 = le12345 .snd .snd .snd .snd
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  le5 $
  ∣ inr (big-step-post-step {a = a₂} {ss = p₂} ex eq₂ (le3 (bf , sin)) le4) ∣₁
big-step-post-step {s}  .{s' = s''} .{i = While b i}  {a} {ss} (ExWhileT {s'} {s''} {b} {i} bt ex₁ ex₂) seq sin stleq =
  let (inv , p , a₀ , q , eq , eq₁) = strip-while-r seq
      le1234 = while-≤ⁱ-r-id {q₁ = λ z → el! (is-true (bval z (BNot b)) × z ∈ inv)}
                             {q₂ = λ z → el! ⌞ z ∈ strip-while-r seq .snd .snd .snd .fst ⌟} $
               subst (λ q → step ss q ≤ⁱ q) eq stleq
      le1 = le1234 .fst
      le2 = le1234 .snd .fst
      le3 = le1234 .snd .snd .fst
      le4 = le1234 .snd .snd .snd
    in
  subst (λ q → s'' ∈ post q) (eq ⁻¹) $
  big-step-post-step {s' = s''} {a = AnWhile inv b p a₀ q} {ss = post a₀} ex₂ (ap (While b) eq₁)
    (big-step-post-step {s' = s'} {a = a₀} {ss = p} ex₁ eq₁ (le2 (bt , le1 ∣ inl sin ∣₁)) le3)
    (while-≤ⁱ-l {q₁ = λ z → el! (is-true (bval z (BNot b)) × z ∈ inv)}
       inv p a₀ q refl
       (le1 ∘ map [ inr , inr ]ᵤ) le2 le3 le4)
big-step-post-step {s}  {s'}        .{i = While b i}  {a} {ss} (ExWhileF {b} {i} bf)                    seq sin stleq =
  let (inv , p , a₀ , q , eq , eq₁) = strip-while-r seq
      le1234 = while-≤ⁱ-r-id {q₁ = λ z → el! (is-true (bval z (BNot b)) × z ∈ inv)}
                             {q₂ = λ z → el! ⌞ z ∈ strip-while-r seq .snd .snd .snd .fst ⌟} $
               subst (λ q → step ss q ≤ⁱ q) eq stleq
      le1 = le1234 .fst
      le4 = le1234 .snd .snd .snd
    in
  subst (λ q → s' ∈ post q) (eq ⁻¹) $
  le4 $
  bf , (le1 ∣ inl sin ∣₁)

