module Nipkow.ACom.Order where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Order.Minmax
open import Data.Sum
open import Data.String
open import Data.Maybe renaming (rec to recᵐ ; elim to elimᵐ)
open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Binary.All2
open import Data.Reflects

open import Order.Base
open import Order.Diagram.Lub
open import Order.SupLattice
open import Order.SupLattice.SmallBasis

open import List1
open import Nipkow.Lang
open import Nipkow.ACom

module AnInstrLeq
  (A : 𝒰 (ℓsuc 0ℓ))
  (leq : A → A → 𝒰)
  where

  open List1.List1

  _≤ⁱ_ : AnInstr A → AnInstr A → 𝒰 (ℓsuc 0ℓ)
  c₁ ≤ⁱ c₂ = (strip c₁ ＝ strip c₂) × All2₁ leq (annos c₁) (annos c₂)

  opaque
    skip-≤ⁱ-intro : ∀ {s s'}
                  → leq s s'
                  → AnSkip s ≤ⁱ AnSkip s'
    skip-≤ⁱ-intro le = refl , [] , le

    skip-≤ⁱ-introl : ∀ {s c s'}
                   → c ＝ AnSkip s' → leq s s'
                   → AnSkip s ≤ⁱ c
    skip-≤ⁱ-introl {s} eq le = subst (AnSkip s ≤ⁱ_) (eq ⁻¹) (skip-≤ⁱ-intro le)

    skip-≤ⁱ-intror : ∀ {s c s'}
                   → c ＝ AnSkip s → leq s s'
                  → c ≤ⁱ AnSkip s'
    skip-≤ⁱ-intror {s'} eq le = subst (_≤ⁱ AnSkip s') (eq ⁻¹) (skip-≤ⁱ-intro le)

    skip-≤ⁱ-eliml : ∀ {s c}
                  → AnSkip s ≤ⁱ c
                  → Σ[ s' ꞉ A ] (c ＝ AnSkip s') × leq s s'
    skip-≤ⁱ-eliml {s} {c} (h1 , h2 , h3) =
      let (s' , eq) = strip-skip-r (h1 ⁻¹) in
      s' , eq , subst (leq s) (ap post eq) h3

    skip-≤ⁱ-elim : ∀ {s s'}
                 → AnSkip s ≤ⁱ AnSkip s'
                 → leq s s'
    skip-≤ⁱ-elim {s} {s'} (h1 , h2 , h3) = h3

    assign-≤ⁱ-intro : ∀ {x e s s'}
                    → leq s s'
                    → AnAssign x e s ≤ⁱ AnAssign x e s'
    assign-≤ⁱ-intro le = refl , [] , le

    assign-≤ⁱ-introl : ∀ {x e s c s'}
                     → c ＝ AnAssign x e s' → leq s s'
                     → AnAssign x e s ≤ⁱ c
    assign-≤ⁱ-introl {x} {e} {s} eq le =
      subst (AnAssign x e s ≤ⁱ_) (eq ⁻¹) (assign-≤ⁱ-intro le)

    assign-≤ⁱ-intror : ∀ {x e s c s'}
                     → c ＝ AnAssign x e s → leq s s'
                     → c ≤ⁱ AnAssign x e s'
    assign-≤ⁱ-intror {x} {e} {s'} eq le =
      subst (_≤ⁱ AnAssign x e s') (eq ⁻¹) (assign-≤ⁱ-intro le)

    assign-≤ⁱ-eliml : ∀ {x e s c}
                → AnAssign x e s ≤ⁱ c
                → Σ[ s' ꞉ A ] (c ＝ AnAssign x e s') × leq s s'
    assign-≤ⁱ-eliml {x} {e} {s} {c} (h1 , h2 , h3) =
      let (s' , eq) = strip-assign-r (h1 ⁻¹) in
      s' , eq , subst (leq s) (ap post eq) h3

    assign-≤ⁱ-elim : ∀ {x e s s'}
                   → AnAssign x e s ≤ⁱ AnAssign x e s'
                   → leq s s'
    assign-≤ⁱ-elim {x} {e} {s} {s'} (h1 , h2 , h3) = h3

    seq-≤ⁱ-intro : ∀ {c₁ c₂ c₃ c₄}
                 → c₁ ≤ⁱ c₃ → c₂ ≤ⁱ c₄
                 → AnSeq c₁ c₂ ≤ⁱ AnSeq c₃ c₄
    seq-≤ⁱ-intro (e₁ , le₁) (e₂ , le₂) = ap² Seq e₁ e₂ , All2₁-++₁ le₁ le₂

    seq-≤ⁱ-introl : ∀ {c₁ c₂ c c₃ c₄}
                  → c ＝ AnSeq c₃ c₄ → c₁ ≤ⁱ c₃ → c₂ ≤ⁱ c₄
                  → AnSeq c₁ c₂ ≤ⁱ c
    seq-≤ⁱ-introl {c₁} {c₂} eq le₁ le₂ =
      subst (AnSeq c₁ c₂ ≤ⁱ_) (eq ⁻¹) (seq-≤ⁱ-intro le₁ le₂)

    seq-≤ⁱ-intror : ∀ {c₁ c₂ c c₃ c₄}
                  → c ＝ AnSeq c₁ c₂ → c₁ ≤ⁱ c₃ → c₂ ≤ⁱ c₄
                  → c ≤ⁱ AnSeq c₃ c₄
    seq-≤ⁱ-intror {c₃} {c₄} eq le₁ le₂ =
      subst (_≤ⁱ AnSeq c₃ c₄) (eq ⁻¹) (seq-≤ⁱ-intro le₁ le₂)

    seq-≤ⁱ-eliml : ∀ {c₁ c₂ c}
             → AnSeq c₁ c₂ ≤ⁱ c
             → Σ[ c₃ ꞉ AnInstr A ] Σ[ c₄ ꞉ AnInstr A ]
                 (c ＝ AnSeq c₃ c₄) × c₁ ≤ⁱ c₃ × c₂ ≤ⁱ c₄
    seq-≤ⁱ-eliml {c₁} {c₂} {c} (h1 , h2) =
      let (a₁ , a₂ , eq₁ , eq₂ , eq₃) = strip-seq-r (h1 ⁻¹)
          (le1 , le2) = All2₁-split
                          (length-annos-same {c₁ = c₁}
                             (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₂ ⁻¹)))
                          (subst (All2₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) eq₁ h2)
         in
        a₁ , a₂ , eq₁ , (eq₂ ⁻¹ , le1) , eq₃ ⁻¹ , le2

    seq-≤ⁱ-elim : ∀ {c₁ c₂ c₃ c₄}
                → AnSeq c₁ c₂ ≤ⁱ AnSeq c₃ c₄
                → c₁ ≤ⁱ c₃ × c₂ ≤ⁱ c₄
    seq-≤ⁱ-elim {c₁} {c₂} le =
      let (a₁ , a₂ , eq , le₁ , le₂) = seq-≤ⁱ-eliml le
          (eq₁ , eq₂) = AnSeq-inj eq
        in
      subst (c₁ ≤ⁱ_) (eq₁ ⁻¹) le₁ , subst (c₂ ≤ⁱ_) (eq₂ ⁻¹) le₂

    ite-≤ⁱ-intro : ∀ {b p₁ c₁ p₂ c₂ q₁ p₃ c₃ p₄ c₄ q₂}
                 → leq p₁ p₃ → c₁ ≤ⁱ c₃ → leq p₂ p₄ → c₂ ≤ⁱ c₄ → leq q₁ q₂
                 → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ AnITE b p₃ c₃ p₄ c₄ q₂
    ite-≤ⁱ-intro {b} le₁ (e₂ , le₂) le₃ (e₄ , le₄) le₅ =
      ( ap² (ITE b) e₂ e₄
      , All2₁-∶+₁-r (All2₁-++₁ (All2-∶∶₁-r le₁ le₂) (All2-∶∶₁-r le₃ le₄)) le₅)

    ite-≤ⁱ-introl : ∀ {b p₁ c₁ p₂ c₂ q₁ c p₃ c₃ p₄ c₄ q₂}
                  → c ＝ AnITE b p₃ c₃ p₄ c₄ q₂
                  → leq p₁ p₃ → c₁ ≤ⁱ c₃ → leq p₂ p₄ → c₂ ≤ⁱ c₄ → leq q₁ q₂
                  → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c
    ite-≤ⁱ-introl {b} {p₁} {c₁} {p₂} {c₂} {q₁} eq le₁ le₂ le₃ le₄ le₅ =
      subst (AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ_) (eq ⁻¹) (ite-≤ⁱ-intro le₁ le₂ le₃ le₄ le₅)

    ite-≤ⁱ-intror : ∀ {b p₁ c₁ p₂ c₂ q₁ c p₃ c₃ p₄ c₄ q₂}
                  → c ＝ AnITE b p₁ c₁ p₂ c₂ q₁
                  → leq p₁ p₃ → c₁ ≤ⁱ c₃ → leq p₂ p₄ → c₂ ≤ⁱ c₄ → leq q₁ q₂
                  → c ≤ⁱ AnITE b p₃ c₃ p₄ c₄ q₂
    ite-≤ⁱ-intror {b} {p₃} {c₃} {p₄} {c₄} {q₂} eq le₁ le₂ le₃ le₄ le₅ =
      subst (_≤ⁱ AnITE b p₃ c₃ p₄ c₄ q₂) (eq ⁻¹) (ite-≤ⁱ-intro le₁ le₂ le₃ le₄ le₅)

    ite-≤ⁱ-eliml : ∀ {b p₁ c₁ p₂ c₂ q₁ c}
                 → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c
                 → Σ[ p₃ ꞉ A ] Σ[ c₃ ꞉ AnInstr A ] Σ[ p₄ ꞉ A ] Σ[ c₄ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                                  (c ＝ AnITE b p₃ c₃ p₄ c₄ q₂)
                                × leq p₁ p₃ × c₁ ≤ⁱ c₃ × leq p₂ p₄ × c₂ ≤ⁱ c₄ × leq q₁ q₂
    ite-≤ⁱ-eliml {b} {p₁} {c₁} {p₂} {c₂} {q₁} {c} (h1 , h2) =
      let (p₃ , a₁ , p₄ , a₂ , q , eq , eq₁ , eq₂) = strip-ite-r (h1 ⁻¹)
          le = All2₁-∶+₁-l (  length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
                            ∙ ap² (λ x y → suc x + suc y)
                                  (length-annos-same {c₁ = c₁}
                                     (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₁ ⁻¹)))
                                  (length-annos-same {c₁ = c₂}
                                     (reflects-true (reflects-instr (strip c₂) (strip a₂)) (eq₂ ⁻¹)))
                            ∙ length₁-++ {xs = p₃ ∷₁ annos a₁} {ys = p₄ ∷₁ annos a₂} ⁻¹) $
                 subst (All2₁ leq (((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₁) ∘ annos) eq h2
          (le₁₁ , le₁₂) = All2₁-split (ap suc (length-annos-same {c₁ = c₁} (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₁ ⁻¹))))
                                      (le .fst)
          (le₂₁ , le₂₂) = All2-∶∶₁-l le₁₁
          (le₃₁ , le₃₂) = All2-∶∶₁-l le₁₂
        in
      p₃ , a₁ , p₄ , a₂ , q , eq , le₂₁ , (eq₁ ⁻¹ , le₂₂) , le₃₁ , (eq₂ ⁻¹ , le₃₂) , le .snd

    ite-≤ⁱ-elim : ∀ {b p₁ c₁ p₂ c₂ q₁ p₃ c₃ p₄ c₄ q₂}
                → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ AnITE b p₃ c₃ p₄ c₄ q₂
                → leq p₁ p₃ × c₁ ≤ⁱ c₃ × leq p₂ p₄ × c₂ ≤ⁱ c₄ × leq q₁ q₂
    ite-≤ⁱ-elim {b} {p₁} {c₁} {p₂} {c₂} {q₁} {p₃} {c₃} {p₄} {c₄} {q₂} le =
      let (r₁ , a₁ , r₂ , a₂ , w₁ , eq , le₁ , le₂ , le₃ , le₄ , le₅) = ite-≤ⁱ-eliml le
          (_ , eq₁ , eq₂ , eq₃ , eq₄ , eq₅) = AnITE-inj eq
        in
        subst (leq p₁) (eq₁ ⁻¹) le₁
      , subst (c₁ ≤ⁱ_) (eq₂ ⁻¹) le₂
      , subst (leq p₂) (eq₃ ⁻¹) le₃
      , subst (c₂ ≤ⁱ_) (eq₄ ⁻¹) le₄
      , subst (leq q₁) (eq₅ ⁻¹) le₅

    while-≤ⁱ-intro : ∀ {inv₁ b p₁ c₁ q₁ inv₂ p₂ c₂ q₂}
                    → leq inv₁ inv₂ → leq p₁ p₂
                    → c₁ ≤ⁱ c₂ → leq q₁ q₂
                    → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ AnWhile inv₂ b p₂ c₂ q₂
    while-≤ⁱ-intro {b} le₁ le₂ (e₃ , le₃) le₄ =
      ( ap (While b) e₃
      , All2₁-∶+₁-r (All2-∶∶₁-r le₁ (All2-∶∶₁-r le₂ le₃)) le₄)

    while-≤ⁱ-introl : ∀ {inv₁ b p₁ c₁ q₁ c inv₂ p₂ c₂ q₂}
                    → c ＝ AnWhile inv₂ b p₂ c₂ q₂
                    → leq inv₁ inv₂ → leq p₁ p₂
                    → c₁ ≤ⁱ c₂ → leq q₁ q₂
                    → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ c
    while-≤ⁱ-introl {inv₁} {b} {p₁} {c₁} {q₁} {c} eq le₁ le₂ le₃ le₄ =
      subst (AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ_) (eq ⁻¹) (while-≤ⁱ-intro le₁ le₂ le₃ le₄)

    while-≤ⁱ-intror : ∀ {inv₁ b p₁ c₁ q₁ c inv₂ p₂ c₂ q₂}
                    → c ＝ AnWhile inv₁ b p₁ c₁ q₁
                    → leq inv₁ inv₂ → leq p₁ p₂
                    → c₁ ≤ⁱ c₂ → leq q₁ q₂
                    → c ≤ⁱ AnWhile inv₂ b p₂ c₂ q₂
    while-≤ⁱ-intror {b} {c} {inv₂} {p₂} {c₂} {q₂} eq le₁ le₂ le₃ le₄ =
      subst (_≤ⁱ AnWhile inv₂ b p₂ c₂ q₂) (eq ⁻¹) (while-≤ⁱ-intro le₁ le₂ le₃ le₄)

    while-≤ⁱ-eliml : ∀ {inv₁ b p₁ c₁ q₁ c}
                   → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ c
                   → Σ[ inv₂ ꞉ A ] Σ[ p₂ ꞉ A ] Σ[ c₂ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                         (c ＝ AnWhile inv₂ b p₂ c₂ q₂)
                       × leq inv₁ inv₂ × leq p₁ p₂ × c₁ ≤ⁱ c₂ × leq q₁ q₂
    while-≤ⁱ-eliml {inv₁} {b} {p₁} {c₁} {q₁} {c} (h1 , h2) =
      let (inv₂ , p , a , q , eq , eq₁) = strip-while-r (h1 ⁻¹)
          le = All2₁-∶+₁-l (ap (2 +_)
                              (length-annos-same {c₁ = c₁}
                                (reflects-true (reflects-instr (strip c₁) (strip a)) (eq₁ ⁻¹)))) $
               subst (All2₁ leq (((inv₁ ∷₁ (p₁ ∷₁ annos c₁)) ∶+₁ q₁)) ∘ annos) eq h2
          (le₁₁ , le₁₂) = All2-∶∶₁-l (le .fst)
          (le₂₁ , le₂₂) = All2-∶∶₁-l le₁₂
       in
      inv₂ , p , a , q , eq , le₁₁ , le₂₁ , (eq₁ ⁻¹ , le₂₂) , le .snd

    while-≤ⁱ-elim : ∀ {b inv₁ p₁ c₁ q₁ inv₂ p₂ c₂ q₂}
                  → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ AnWhile inv₂ b p₂ c₂ q₂
                  → leq inv₁ inv₂ × leq p₁ p₂ × c₁ ≤ⁱ c₂ × leq q₁ q₂
    while-≤ⁱ-elim {b} {inv₁} {p₁} {c₁} {q₁} {inv₂} {p₂} {c₂} {q₂} le =
      let (inv₀ , p , a , q , eq , le1 , le2 , le3 , le4) = while-≤ⁱ-eliml le
          (eq₁ , _ , eq₂ , eq₃ , eq₄) = AnWhile-inj eq
        in
        subst (leq inv₁) (eq₁ ⁻¹) le1
      , subst (leq p₁) (eq₂ ⁻¹) le2
      , subst (c₁ ≤ⁱ_) (eq₃ ⁻¹) le3
      , subst (leq q₁) (eq₄ ⁻¹) le4

  mono-post : ∀ {c₁ c₂} → c₁ ≤ⁱ c₂ → leq (post c₁) (post c₂)
  mono-post (_ , _ , h) = h

module AnInstrOrd {B : 𝒰}
  (P : Poset (ℓsuc 0ℓ) 0ℓ)
  (L : is-sup-lattice P 0ℓ)
  (β : B → ⌞ P ⌟)
  (h : is-basis P L β)
  where

  open Poset P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open AnInstrLeq Ob _≤_

  -- TODO reuse Order.Diagram.Lub.Reasoning
  P⊥ : Ob
  P⊥ = sup {I = ⊥} λ ()

  P⊥≤ : ∀ {o} → P⊥ ≤ o
  P⊥≤ {o} = suprema (λ ()) .least o λ ()

  an-poset : Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  an-poset .Poset.Ob                                = AnInstr Ob
  an-poset .Poset._≤_                               = _≤ⁱ_
  an-poset .Poset.≤-thin                            = ×-is-of-hlevel 1 (instr-is-set (strip _) (strip _))
                                                                       (All2₁-is-of-hlevel 0 (λ _ _ → ≤-thin))
  an-poset .Poset.≤-refl                            = refl , all2₁-refl (λ _ → ≤-refl)
  an-poset .Poset.≤-trans (exy , axy) (eyz , ayz)   = exy ∙ eyz , all2₁-trans (λ _ _ _ → ≤-trans) axy ayz
  an-poset .Poset.≤-antisym (exy , axy) (eyx , ayx) =
    strip-annos-same (reflects-true (reflects-instr (strip _) (strip _)) exy)
                     (all2₁-antisym (λ _ _ → ≤-antisym) axy ayx)

  anc-poset : Instr → Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  anc-poset c .Poset.Ob = AnStr Ob c
  anc-poset c .Poset._≤_ (a1 , e1) (a2 , e2) = a1 ≤ⁱ a2  -- TODO try just all2 leq, because strip equality is assumed
  anc-poset c .Poset.≤-thin = ×-is-of-hlevel 1 (instr-is-set (strip _) (strip _))
                                               (All2₁-is-of-hlevel 0 (λ _ _ → ≤-thin))
  anc-poset c .Poset.≤-refl = refl , all2₁-refl (λ _ → ≤-refl)
  anc-poset c .Poset.≤-trans (exy , axy) (eyz , ayz)   = exy ∙ eyz , all2₁-trans (λ _ _ _ → ≤-trans) axy ayz
  anc-poset c .Poset.≤-antisym {x = ax , ex} {y = ay , ey} (exy , axy) (eyx , ayx) =
    Σ-prop-path (λ a → instr-is-set (strip a) c) $
    strip-annos-same (reflects-true (reflects-instr (strip _) (strip _)) exy)
                     (all2₁-antisym (λ _ _ → ≤-antisym) axy ayx)

  anc-sup : ∀ (c : Instr) → {I : 𝒰} → (I → AnStr Ob c) → AnStr Ob c
  anc-sup  Skip         F =
    AnSkip (sup λ i → let (a , e) = strip-skip-r (F i .snd) in a) , refl
  anc-sup (Assign x e)  F =
    AnAssign x e (sup λ i → let (a , e) = strip-assign-r (F i .snd) in a) , refl
  anc-sup (Seq c₁ c₂)   F =
    let (a₁ , e₁) = anc-sup c₁ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₁ , e₁
        (a₂ , e₂) = anc-sup c₂ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₂ , e₂
     in
    AnSeq a₁ a₂ , ap² Seq e₁ e₂
  anc-sup (ITE b c₁ c₂) F =
    let (a₁ , e₁) = anc-sup c₁ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₁ , e₁
        (a₂ , e₂) = anc-sup c₂ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₂ , e₂
     in
   AnITE b
     (sup λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₁)
     a₁
     (sup λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₂)
     a₂
     (sup λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in q)
   , ap² (ITE b) e₁ e₂
  anc-sup (While b c)   F =
    let (a , e) = anc-sup c λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in a , e
     in
    AnWhile (sup λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in inv)
            b
            (sup λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in p)
            a
            (sup λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in q)
    , ap (While b) e

  anc-lub : ∀ c {I : 𝒰} (F : I → AnStr Ob c)
          → is-lub (anc-poset c) F (anc-sup c F)
  anc-lub  Skip         F =
    let a  = sup     λ j → let (a , _) = strip-skip-r (F j .snd) in a
        sa = suprema λ j → let (a , _) = strip-skip-r (F j .snd) in a
      in
    record {
      fam≤lub = λ i → skip-≤ⁱ-intror (let (a , e) = strip-skip-r (F i .snd) in e) $
                      sa .fam≤lub i
    ; least = λ where (a' , eq) f →
                         let (a1 , eq1) = strip-skip-r eq in
                         skip-≤ⁱ-introl eq1 $
                         sa .least a1 λ i → skip-≤ⁱ-elim $
                                            subst (_≤ⁱ AnSkip a1) (let (a , e) = strip-skip-r (F i .snd) in e) $
                                            subst (F i .fst ≤ⁱ_) eq1 (f i)
    }
  anc-lub (Assign x e)  F =
    let a  = sup     λ j → let (a , e) = strip-assign-r (F j .snd) in a
        sa = suprema λ j → let (a , e) = strip-assign-r (F j .snd) in a
      in
    record {
      fam≤lub = λ i → assign-≤ⁱ-intror (let (a , e) = strip-assign-r (F i .snd) in e) $
                      sa .fam≤lub i
    ; least = λ where (a' , eq) f →
                          let (a1 , eq1) = strip-assign-r eq in
                          assign-≤ⁱ-introl eq1 $
                          sa .least a1 λ i → assign-≤ⁱ-elim $
                                             subst (_≤ⁱ AnAssign x e a1) (let (_ , e) = strip-assign-r (F i .snd) in e) $
                                             subst (F i .fst ≤ⁱ_) eq1 (f i)
    }
  anc-lub (Seq c₁ c₂)   F =
    let (a₁ , _) = anc-sup c₁ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₁ , e₁
        ih₁      = anc-lub c₁ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₁ , e₁
        (a₂ , _) = anc-sup c₂ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₂ , e₂
        ih₂      = anc-lub c₂ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₂ , e₂
     in
    record {
      fam≤lub = λ i → seq-≤ⁱ-intror (let (_ , _ , eq' , _ , _) = strip-seq-r (F i .snd) in eq')
                         (ih₁ .fam≤lub i) (ih₂ .fam≤lub i)
    ; least = λ where (a' , eq) f →
                          let (a1 , a2 , eq0 , eq1 , eq2) = strip-seq-r eq in
                          seq-≤ⁱ-introl eq0
                            (ih₁ .least (a1 , eq1) λ i → let le12 = seq-≤ⁱ-elim $
                                                                    subst (_≤ⁱ AnSeq a1 a2) (let (_ , _ , e , _ , _) = strip-seq-r (F i .snd) in e) $
                                                                    subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                         le12 .fst)
                            (ih₂ .least (a2 , eq2) λ i → let le12 = seq-≤ⁱ-elim $
                                                                    subst (_≤ⁱ AnSeq a1 a2) (let (_ , _ , e , _ , _) = strip-seq-r (F i .snd) in e) $
                                                                    subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                         le12 .snd)
    }
  anc-lub (ITE b c₁ c₂) F =
    let p₁  = sup     λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₁
        sp₁ = suprema λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₁
        (a₁ , _) = anc-sup c₁ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₁ , e₁
        ih₁      = anc-lub c₁ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₁ , e₁
        p₂  = sup     λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₂
        sp₂ = suprema λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₂
        (a₂ , _) = anc-sup c₂ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₂ , e₂
        ih₂      = anc-lub c₂ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₂ , e₂
        q  = sup     λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in q
        sq = suprema λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in q
      in
    record {
      fam≤lub = λ i → ite-≤ⁱ-intror (let (_ , _ , _ , _ , _ , eq' , _ , _) = strip-ite-r (F i .snd) in eq')
                        (sp₁ .fam≤lub i) (ih₁ .fam≤lub i) (sp₂ .fam≤lub i) (ih₂ .fam≤lub i) (sq .fam≤lub i)
    ; least = λ where (a' , eq) f →
                          let (p1 , a1 , p2 , a2 , q0 , eq0 , e1 , e2) = strip-ite-r eq in
                          ite-≤ⁱ-introl eq0
                            (sp₁ .least p1 λ i → let le12345 = ite-≤ⁱ-elim $
                                                               subst (_≤ⁱ AnITE b p1 a1 p2 a2 q0) (let (_ , _ , _ , _ , _ , e' , _ , _) = strip-ite-r (F i .snd) in e') $
                                                               subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                 le12345 .fst)
                            (ih₁ .least (a1 , e1) λ i → let le12345 = ite-≤ⁱ-elim $
                                                                      subst (_≤ⁱ AnITE b p1 a1 p2 a2 q0) (let (_ , _ , _ , _ , _ , e' , _ , _) = strip-ite-r (F i .snd) in e') $
                                                                      subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                        le12345 .snd .fst)
                            (sp₂ .least p2 λ i → let le12345 = ite-≤ⁱ-elim $
                                                               subst (_≤ⁱ AnITE b p1 a1 p2 a2 q0) (let (_ , _ , _ , _ , _ , e' , _ , _) = strip-ite-r (F i .snd) in e') $
                                                               subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                 le12345 .snd .snd .fst)
                            (ih₂ .least (a2 , e2) λ i → let le12345 = ite-≤ⁱ-elim $
                                                                      subst (_≤ⁱ AnITE b p1 a1 p2 a2 q0) (let (_ , _ , _ , _ , _ , e' , _ , _) = strip-ite-r (F i .snd) in e') $
                                                                      subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                        le12345 .snd .snd .snd .fst)
                            (sq .least q0 λ i → let le12345 = ite-≤ⁱ-elim $
                                                              subst (_≤ⁱ AnITE b p1 a1 p2 a2 q0) (let (_ , _ , _ , _ , _ , e' , _ , _) = strip-ite-r (F i .snd) in e') $
                                                              subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                le12345 .snd .snd .snd .snd)
    }
  anc-lub (While b c)   F =
    let inv  = sup     λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in inv
        sinv = suprema λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in inv
        p  = sup     λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in p
        sp = suprema λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in p
        (a , _) = anc-sup c λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in a , e
        ih      = anc-lub c λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in a , e
        q  = sup     λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in q
        sq = suprema λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in q
      in
    record {
      fam≤lub = λ i → while-≤ⁱ-intror (let (_ , _ , _ , _ , eq' , _) = strip-while-r (F i .snd) in eq')
                        (sinv .fam≤lub i) (sp .fam≤lub i) (ih .fam≤lub i) (sq .fam≤lub i)
    ; least = λ where (a' , eq) f →
                        let (inv1 , p1 , a1 , q1 , eq0 , e1) = strip-while-r eq in
                        while-≤ⁱ-introl eq0
                          (sinv .least inv1 λ i → let le1234 = while-≤ⁱ-elim $
                                                               subst (_≤ⁱ AnWhile inv1 b p1 a1 q1) (let (_ , _ , _ , _ , e' , _) = strip-while-r (F i .snd) in e') $
                                                               subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                  le1234 .fst)
                          (sp .least p1 λ i → let le1234 = while-≤ⁱ-elim $
                                                           subst (_≤ⁱ AnWhile inv1 b p1 a1 q1) (let (_ , _ , _ , _ , e' , _) = strip-while-r (F i .snd) in e') $
                                                           subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                              le1234 .snd .fst)
                          (ih .least (a1 , e1) λ i → let le1234 = while-≤ⁱ-elim $
                                                                  subst (_≤ⁱ AnWhile inv1 b p1 a1 q1) (let (_ , _ , _ , _ , e' , _) = strip-while-r (F i .snd) in e') $
                                                                  subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                                     le1234 .snd .snd .fst)
                          (sq .least q1 λ i → let le1234 = while-≤ⁱ-elim $
                                                           subst (_≤ⁱ AnWhile inv1 b p1 a1 q1) (let (_ , _ , _ , _ , e' , _) = strip-while-r (F i .snd) in e') $
                                                           subst (F i .fst ≤ⁱ_) eq0 (f i) in
                                              le1234 .snd .snd .snd)
    }

  anc-suplat : (c : Instr) → is-sup-lattice (anc-poset c) 0ℓ
  anc-suplat c .is-sup-lattice.sup = anc-sup c
  anc-suplat c .is-sup-lattice.suprema = anc-lub c

  -- TODO use state monad
  un-β : Maybe (B × List B) → Ob × List B
  un-β = recᵐ (P⊥ , []) (first β)

  uncons-β : List B → Ob × List B
  uncons-β = un-β ∘ unconsᵐ

  anc-β-aux : (c : Instr) → List B → AnStr Ob c × List B
  anc-β-aux  Skip         zs =
    let (p , zs₀) = uncons-β zs in
    (AnSkip p , refl) , zs₀
  anc-β-aux (Assign x e) zs =
    let (p , zs₀) = uncons-β zs in
    (AnAssign x e p , refl) , zs₀
  anc-β-aux (Seq c₁ c₂)   zs =
    let ((a₁ , e₁) , zs₀) = anc-β-aux c₁ zs
        ((a₂ , e₂) , zs₁) = anc-β-aux c₂ zs₀
     in
    (AnSeq a₁ a₂ , ap² Seq e₁ e₂) , zs₁
  anc-β-aux (ITE b c₁ c₂) zs =
    let (p₀        , zs₀) = uncons-β zs
        ((a₁ , e₁) , zs₁) = anc-β-aux c₁ zs₀
        (p₁        , zs₂) = uncons-β zs₁
        ((a₂ , e₂) , zs₃) = anc-β-aux c₂ zs₂
        (p₂        , zs₄) = uncons-β zs₃
      in
    (AnITE b p₀ a₁ p₁ a₂ p₂ , ap² (ITE b) e₁ e₂) , zs₄
  anc-β-aux (While b c)   zs =
    let (p₀      , zs₀) = uncons-β zs
        (p₁      , zs₁) = uncons-β zs₀
        ((a , e) , zs₂) = anc-β-aux c zs₁
        (p₂      , zs₃) = uncons-β zs₂
      in
    (AnWhile p₀ b p₁ a p₂ , ap (While b) e) , zs₃

  anc-β : (c : Instr) → List B → AnStr Ob c
  anc-β c zs = anc-β-aux c zs .fst

  -- TODO move to AnCom
  ann-count : Instr → ℕ
  ann-count  Skip         = 1
  ann-count (Assign x e)  = 1
  ann-count (Seq c₁ c₂)   = ann-count c₁ + ann-count c₂
  ann-count (ITE b c₁ c₂) = 3 + ann-count c₁ + ann-count c₂
  ann-count (While b c)   = 3 + ann-count c
