module Nipkow.ACom.Order where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat renaming (_==_ to _==ⁿ_ ; rec to recⁿ ; ==-reflects to ==ⁿ-reflects)
open import Data.Nat.Order.Base
  renaming ( _≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_
           ; ≤-refl to ≤ⁿ-refl ; ≤-trans to ≤ⁿ-trans ; ≤-antisym to ≤ⁿ-antisym)
open import Data.Nat.Order.Inductive.Base using (_≤?_)
open import Data.Nat.Order.Minmax
open import Data.Sum
open import Data.String
open import Data.Maybe renaming (rec to recᵐ ; elim to elimᵐ)
open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Correspondences.Binary.All
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
  c₁ ≤ⁱ c₂ = (strip c₁ ＝ strip c₂) × All²₁ leq (annos c₁) (annos c₂)

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
    seq-≤ⁱ-intro (e₁ , le₁) (e₂ , le₂) = ap² Seq e₁ e₂ , All²₁-++₁ le₁ le₂

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
          (le1 , le2) = All²₁-split
                          (length-annos-same {c₁ = c₁}
                             (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₂ ⁻¹)))
                          (subst (All²₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) eq₁ h2)
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
      , All²₁-∶+₁-r (All²₁-++₁ (All²-∶∶₁-r le₁ le₂) (All²-∶∶₁-r le₃ le₄)) le₅)

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
          le = All²₁-∶+₁-l (  length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
                            ∙ ap² (λ x y → suc x + suc y)
                                  (length-annos-same {c₁ = c₁}
                                     (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₁ ⁻¹)))
                                  (length-annos-same {c₁ = c₂}
                                     (reflects-true (reflects-instr (strip c₂) (strip a₂)) (eq₂ ⁻¹)))
                            ∙ length₁-++ {xs = p₃ ∷₁ annos a₁} {ys = p₄ ∷₁ annos a₂} ⁻¹) $
                 subst (All²₁ leq (((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₁) ∘ annos) eq h2
          (le₁₁ , le₁₂) = All²₁-split (ap suc (length-annos-same {c₁ = c₁} (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₁ ⁻¹))))
                                      (le .fst)
          (le₂₁ , le₂₂) = All²-∶∶₁-l le₁₁
          (le₃₁ , le₃₂) = All²-∶∶₁-l le₁₂
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
      , All²₁-∶+₁-r (All²-∶∶₁-r le₁ (All²-∶∶₁-r le₂ le₃)) le₄)

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
          le = All²₁-∶+₁-l (ap (2 +_)
                              (length-annos-same {c₁ = c₁}
                                (reflects-true (reflects-instr (strip c₁) (strip a)) (eq₁ ⁻¹)))) $
               subst (All²₁ leq (((inv₁ ∷₁ (p₁ ∷₁ annos c₁)) ∶+₁ q₁)) ∘ annos) eq h2
          (le₁₁ , le₁₂) = All²-∶∶₁-l (le .fst)
          (le₂₁ , le₂₂) = All²-∶∶₁-l le₁₂
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

  an-poset : Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  an-poset .Poset.Ob                                = AnInstr Ob
  an-poset .Poset._≤_                               = _≤ⁱ_
  an-poset .Poset.≤-thin                            = ×-is-of-hlevel 1 (instr-is-set (strip _) (strip _))
                                                                       (All²₁-is-of-hlevel 0 (λ _ _ → ≤-thin))
  an-poset .Poset.≤-refl                            = refl , all²₁-refl (λ _ → ≤-refl)
  an-poset .Poset.≤-trans (exy , axy) (eyz , ayz)   = exy ∙ eyz , all²₁-trans (λ _ _ _ → ≤-trans) axy ayz
  an-poset .Poset.≤-antisym (exy , axy) (eyx , ayx) =
    strip-annos-same (reflects-true (reflects-instr (strip _) (strip _)) exy)
                     (all²₁-antisym (λ _ _ → ≤-antisym) axy ayx)

  anc-poset : Instr → Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  anc-poset c .Poset.Ob = AnStr Ob c
  anc-poset c .Poset._≤_ (a1 , e1) (a2 , e2) = a1 ≤ⁱ a2  -- TODO try just all2 leq, because strip equality is assumed
  anc-poset c .Poset.≤-thin = ×-is-of-hlevel 1 (instr-is-set (strip _) (strip _))
                                               (All²₁-is-of-hlevel 0 (λ _ _ → ≤-thin))
  anc-poset c .Poset.≤-refl = refl , all²₁-refl (λ _ → ≤-refl)
  anc-poset c .Poset.≤-trans (exy , axy) (eyz , ayz)   = exy ∙ eyz , all²₁-trans (λ _ _ _ → ≤-trans) axy ayz
  anc-poset c .Poset.≤-antisym {x = ax , ex} {y = ay , ey} (exy , axy) (eyx , ayx) =
    Σ-prop-path (λ a → instr-is-set (strip a) c) $
    strip-annos-same (reflects-true (reflects-instr (strip _) (strip _)) exy)
                     (all²₁-antisym (λ _ _ → ≤-antisym) axy ayx)

  anc-sup : ∀ (c : Instr) → {I : 𝒰} → (I → AnStr Ob c) → AnStr Ob c
  anc-sup  Skip         {I} F =
    AnSkip (⋃ λ i → let (a , e) = strip-skip-r (F i .snd) in a) , refl
  anc-sup (Assign x e)  F =
    AnAssign x e (⋃ λ i → let (a , e) = strip-assign-r (F i .snd) in a) , refl
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
     (⋃ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₁)
     a₁
     (⋃ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₂)
     a₂
     (⋃ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in q)
   , ap² (ITE b) e₁ e₂
  anc-sup (While b c)   F =
    let (a , e) = anc-sup c λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in a , e
     in
    AnWhile (⋃ λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in inv)
            b
            (⋃ λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in p)
            a
            (⋃ λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in q)
    , ap (While b) e

  anc-lub : ∀ c {I : 𝒰} (F : I → AnStr Ob c)
          → is-lub (anc-poset c) F (anc-sup c F)
  anc-lub  Skip         F =
    let sa = lubs (λ j → let (a , _) = strip-skip-r (F j .snd) in a) .Lub.has-lub in
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
    let sa = lubs (λ j → let (a , e) = strip-assign-r (F j .snd) in a) .Lub.has-lub in
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
    let ih₁ = anc-lub c₁ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₁ , e₁
        ih₂ = anc-lub c₂ λ i → let (a₁ , a₂ , eq , e₁ , e₂) = strip-seq-r (F i .snd) in a₂ , e₂
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
    let sp₁ = lubs      (λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₁) .Lub.has-lub
        ih₁ = anc-lub c₁ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₁ , e₁
        sp₂ = lubs      (λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in p₂) .Lub.has-lub
        ih₂ = anc-lub c₂ λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in a₂ , e₂
        sq  = lubs      (λ i → let (p₁ , a₁ , p₂ , a₂ , q , eq , e₁ , e₂) = strip-ite-r (F i .snd) in q) .Lub.has-lub
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
    let sinv = lubs     (λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in inv) .Lub.has-lub
        sp   = lubs     (λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in p) .Lub.has-lub
        ih   = anc-lub c λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in a , e
        sq   = lubs     (λ i → let (inv , p , a , q , eq , e) = strip-while-r (F i .snd) in q) .Lub.has-lub
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
  anc-suplat c .is-sup-lattice.has-lubs {F} .Lub.lub = anc-sup c F
  anc-suplat c .is-sup-lattice.has-lubs {F} .Lub.has-lub = anc-lub c F

  annotate-bot : ∀ {c a}
               → strip a ＝ c
               → annotate (λ _ → bot) c ≤ⁱ a
  annotate-bot {c} {a} e =
    ( strip-annotate ∙ e ⁻¹
    , subst (λ q → All²₁ _≤_ q (annos a))
            (annos-annotate-const ⁻¹)
            (subst (λ q → All²₁ _≤_ (replicate₁ q bot) (annos a))
                   (length₁-annos {a = a} ∙ ap asize e)
                   (All²₁-replicate-l has-bot)))

  unᵐ-β : Maybe B → Ob
  unᵐ-β = recᵐ bot β

  shr : (ℕ → Maybe B) → ℕ → ℕ → Maybe B
  shr f n k = if n ≤? k then f (k ∸ n) else nothing

  single-at : B → ℕ → ℕ → Maybe B
  single-at b n k = if n ==ⁿ k then just b else nothing

  annotate-β : (c : Instr) → (ℕ → Maybe B) → AnInstr Ob
  annotate-β c f = annotate (unᵐ-β ∘ f) c

  filt : (ℕ → Maybe B) → (ℕ → Bool) → ℕ → Maybe B
  filt f p n = if p n then f n else nothing

  annotate-β-filt : ∀ {c : Instr} {f : ℕ → Maybe B} {p : ℕ → Bool}
                  → (∀ n → n <ⁿ asize c → is-true (p n))
                  → annotate-β c (filt f p) ＝ annotate-β c f
  annotate-β-filt h = annotate-ext λ n lt → ap unᵐ-β (if-true (h n lt))

{-
  shl-filt : {f : ℕ → Maybe B} {p : ℕ → Bool} {n : ℕ}
             → (∀ m → n ≤ⁿ m → is-true (p m))
             → shl (unᵐ-β ∘ filt f p) n ＝ unᵐ-β ∘ shl f n
  shl-filt {n} h = fun-ext λ k → ap unᵐ-β (if-true (h (k + n) ≤-+-l))
-}

  shl-shr : {f : ℕ → Maybe B} {n : ℕ}
          → shl (unᵐ-β ∘ shr f n) n ＝ unᵐ-β ∘ f
  shl-shr {f} {n} = fun-ext λ k → ap unᵐ-β (if-true (reflects-true (≤-reflects n (k + n)) ≤-+-l) ∙ ap f (+-cancel-∸-r k n))

  shl-filt-not : {f : ℕ → Maybe B} {p : ℕ → Bool} {n : ℕ}
                 → (∀ m → n ≤ⁿ m → is-true (not (p m)))
                 → shl (unᵐ-β ∘ filt f p) n ＝ λ _ → bot
  shl-filt-not {n} h = fun-ext λ k → ap unᵐ-β (if-false (h (k + n) ≤-+-l))

  shl-single-at-not : {b : B} {n m : ℕ}
                  → n <ⁿ m
                  → shl (unᵐ-β ∘ single-at b n) m ＝ λ _ → bot
  shl-single-at-not {n} {m} lt = fun-ext λ k → ap unᵐ-β (if-false (reflects-false (==ⁿ-reflects n (k + m))
                                                                     (contra (λ e → subst (m ≤ⁿ_) (e ⁻¹) ≤-+-l) (<→≱ $ lt))))

  anc-β : (c : Instr) → (ℕ → Maybe B) → AnStr Ob c
  anc-β c f = annotate-β c f , strip-annotate

  anc-bas : ∀ c → is-basis (anc-poset c) (anc-suplat c) (anc-β c)
  anc-bas  Skip         =
    record {
      ≤-is-small = λ where (a , e) zs → size 0ℓ ⦃ s = Size-Σ ⦃ sa = Size-default ⦄ ⦄
    ; ↓-is-sup = λ where (a , e) →
                           let (o' , e') = strip-skip-r e
                               su = ↓-is-sup o'
                             in
                            record {
                              fam≤lub = λ where (bf , le) → le
                            ; least = λ where (a'' , e'') f →
                                                let (oo , eo) = strip-skip-r e'' in
                                                subst (_≤ⁱ a'') (e' ⁻¹) $
                                                skip-≤ⁱ-introl eo (su .least oo λ where (b , le) →
                                                                                          skip-≤ⁱ-elim $
                                                                                          subst (AnSkip (β b) ≤ⁱ_) eo $
                                                                                          f (single-at b 0 , skip-≤ⁱ-introl e' le))
                            } }
  anc-bas (Assign x e)  =
    record {
      ≤-is-small = λ where (a , eq) zs → size 0ℓ ⦃ s = Size-Σ ⦃ sa = Size-default ⦄ ⦄
    ; ↓-is-sup = λ where (a , eq) →
                           let (o' , eq') = strip-assign-r eq
                               su = ↓-is-sup o'
                             in
                            record {
                              fam≤lub = λ where (bf , le) → le
                            ; least = λ where (a'' , eq'') f →
                                                let (oo , eo) = strip-assign-r eq'' in
                                                subst (_≤ⁱ a'') (eq' ⁻¹) $
                                                assign-≤ⁱ-introl eo (su .least oo λ where (b , le) →
                                                                                            assign-≤ⁱ-elim $
                                                                                            subst (AnAssign x e (β b) ≤ⁱ_) eo $
                                                                                            f (single-at b 0 , assign-≤ⁱ-introl eq' le))
                            } }
  anc-bas (Seq c₁ c₂)   =
    let ih₁ = anc-bas c₁
        ih₂ = anc-bas c₂
      in
    record {
      ≤-is-small = λ where (a , e) z → size 0ℓ ⦃ s = Size-Σ ⦃ sa = Size-default ⦄ ⦄
    ; ↓-is-sup = λ where (a , eq) →
                           let (a₁ , a₂ , eq₀ , e₁ , e₂) = strip-seq-r eq in
                           record {
                             fam≤lub = λ where (bf , le) →
                                                  let (a1 , a2 , eq0 , le1 , le2) = seq-≤ⁱ-eliml le
                                                      (e1 , e2) = AnSeq-inj (eq0 ⁻¹ ∙ eq₀)
                                                    in
                                                  seq-≤ⁱ-introl eq0
                                                     (ih₁ .is-basis.↓-is-sup (a1 , ap strip e1 ∙ e₁) .fam≤lub (bf , le1))
                                                     (ih₂ .is-basis.↓-is-sup (a2 , ap strip e2 ∙ e₂) .fam≤lub (shl bf (asize c₁) , le2))
                           ; least = λ where (a'' , eq'') f →
                                               let (a₁' , a₂' , eq₀' , e₁' , e₂') = strip-seq-r eq'' in
                                               subst (_≤ⁱ a'') (eq₀ ⁻¹) $
                                               seq-≤ⁱ-introl eq₀'
                                                 (ih₁ .is-basis.↓-is-sup (a₁ , e₁) .least (a₁' , e₁')
                                                    λ where (bf , le) →
                                                                subst (_≤ⁱ a₁') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt))
                                                                  ((seq-≤ⁱ-elim $
                                                                    subst (AnSeq (annotate-β c₁ (filt bf (_<? asize c₁)))
                                                                                 (annotate-β c₂ (shl (filt bf (_<? asize c₁)) (asize c₁))) ≤ⁱ_)
                                                                          eq₀' $
                                                                    f ( filt bf (_<? asize c₁)
                                                                      , seq-≤ⁱ-introl eq₀
                                                                          (subst (_≤ⁱ a₁) (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt) ⁻¹) le)
                                                                          (subst (λ q → annotate q c₂ ≤ⁱ a₂)
                                                                                 (shl-filt-not {f = bf} {p = _<? asize c₁} {n = asize c₁}
                                                                                    (λ m le → reflects-false (<-reflects m (asize c₁)) (≤≃≯ $ le)) ⁻¹)
                                                                                 (annotate-bot e₂))))
                                                                    .fst))
                                                 (ih₂ .is-basis.↓-is-sup (a₂ , e₂) .least (a₂' , e₂')
                                                    λ where (bf , le) →
                                                               subst (λ q → annotate q c₂ ≤ⁱ a₂') (shl-shr {f = bf} {n = asize c₁})
                                                                 ((seq-≤ⁱ-elim $
                                                                   subst (AnSeq (annotate-β c₁ (shr bf (asize c₁)))
                                                                                (annotate-β c₂ (shl (shr bf (asize c₁)) (asize c₁))) ≤ⁱ_)
                                                                          eq₀' $
                                                                   f ( shr bf (asize c₁)
                                                                     , seq-≤ⁱ-introl eq₀
                                                                         (subst (_≤ⁱ a₁)
                                                                                (annotate-ext {c = c₁} {f = λ _ → bot} {g = unᵐ-β ∘ shr bf (asize c₁)}
                                                                                                λ n lt → ap unᵐ-β (if-false {b = asize c₁ ≤? n} (reflects-false (≤-reflects (asize c₁) n) (<≃≱ $ lt))) ⁻¹)
                                                                                (annotate-bot e₁))
                                                                         (subst (λ q → annotate q c₂ ≤ⁱ a₂) (shl-shr {f = bf} {n = asize c₁} ⁻¹) le)))
                                                                   .snd))

                           } }
  anc-bas (ITE b c₁ c₂) =
    let ih₁ = anc-bas c₁
        ih₂ = anc-bas c₂
     in
    record {
      ≤-is-small = λ where (a , e) z → size 0ℓ ⦃ s = Size-Σ ⦃ sa = Size-default ⦄ ⦄
    ; ↓-is-sup = λ where (a , eq) →
                           let (p₁ , a₁ , p₂ , a₂ , q , eq₀ , e₁ , e₂) = strip-ite-r eq in
                           record {
                             fam≤lub = λ where (bf , le) →
                                                 let (p1 , a1 , p2 , a2 , q0 , eq0 , le1 , le2 , le3 , le4 , le5) = ite-≤ⁱ-eliml le
                                                     (_ , _ , e2 , _ , e4 , _) = AnITE-inj (eq0 ⁻¹ ∙ eq₀)
                                                   in
                                                 ite-≤ⁱ-introl eq0 le1
                                                   (ih₁ .is-basis.↓-is-sup (a1 , ap strip e2 ∙ e₁) .fam≤lub (shl bf 1 , le2))
                                                   le3
                                                   (ih₂ .is-basis.↓-is-sup (a2 , ap strip e4 ∙ e₂) .fam≤lub (shl bf (2 + asize c₁) , le4))
                                                   le5
                           ; least = λ where (a'' , eq'') f →
                                               let (p₁' , a₁' , p₂' , a₂' , q' , eq₀' , e₁' , e₂') = strip-ite-r eq'' in
                                               subst (_≤ⁱ a'') (eq₀ ⁻¹) $
                                               ite-≤ⁱ-introl eq₀'
                                                 (↓-is-sup p₁ .least p₁'
                                                    λ where (b' , le) →
                                                               (ite-≤ⁱ-elim $
                                                                subst (AnITE b (β b') (annotate (shl (unᵐ-β ∘ single-at b' 0) 1) c₁) bot
                                                                                      (annotate (shl (unᵐ-β ∘ single-at b' 0) (2 + asize c₁)) c₂) bot ≤ⁱ_) eq₀' $
                                                                f ( single-at b' 0
                                                                  , ite-≤ⁱ-introl eq₀ le
                                                                       (subst (λ q → annotate q c₁ ≤ⁱ a₁) (shl-single-at-not z<s ⁻¹)
                                                                              (annotate-bot e₁))
                                                                       (has-bot p₂)
                                                                       (subst (λ q → annotate q c₂ ≤ⁱ a₂) (shl-single-at-not z<s ⁻¹)
                                                                              (annotate-bot e₂))
                                                                       (has-bot q)))
                                                                .fst)
                                                 (ih₁ .is-basis.↓-is-sup (a₁ , e₁) .least (a₁' , e₁')
                                                     λ where (bf , le) →
                                                               subst (_≤ⁱ a₁') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt)) $
                                                               subst (λ q → annotate q c₁ ≤ⁱ a₁') (shl-shr {f = filt bf (_<? asize c₁)} {n = 1}) $
                                                               ite-≤ⁱ-elim
                                                                  (subst (AnITE b bot
                                                                            (annotate (shl (unᵐ-β ∘ shr (filt bf (_<? asize c₁)) 1) 1) c₁)
                                                                            (unᵐ-β (shr (filt bf (_<? asize c₁)) 1 (1 + asize c₁)))
                                                                            (annotate (shl (unᵐ-β ∘ shr (filt bf (_<? asize c₁)) 1) (2 + asize c₁)) c₂)
                                                                            (unᵐ-β (shr (filt bf (_<? asize c₁)) 1 (2 + asize c₁ + asize c₂))) ≤ⁱ_) eq₀' $
                                                                   f ( shr (filt bf (_<? asize c₁)) 1
                                                                     , ite-≤ⁱ-introl eq₀
                                                                          (has-bot p₁)
                                                                          (subst (λ q → annotate q c₁ ≤ⁱ a₁) (shl-shr {f = filt bf (_<? asize c₁)} {n = 1} ⁻¹) $
                                                                           subst (_≤ⁱ a₁) (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt) ⁻¹) le)
                                                                          (subst (λ q → unᵐ-β q ≤ p₂) (if-false (reflects-false (<-reflects (asize c₁) (asize c₁)) <-irr) ⁻¹)
                                                                              (has-bot p₂))
                                                                          (subst (_≤ⁱ a₂)
                                                                                 (annotate-ext λ n lt → ap unᵐ-β (  if-true (reflects-true (<-reflects 0 (n + (2 + asize c₁)))
                                                                                                                                           (<-+-l z<s))
                                                                                                                  ∙ if-false (reflects-false (<-reflects (n + (2 + asize c₁) ∸ 1) (asize c₁))
                                                                                                                                             (≤→≯ $ ≤ⁿ-trans (≤ⁿ-trans ≤-ascend ≤-+-l)
                                                                                                                                                      (=→≤ (ap (_∸ 1) (+-suc-r n (1 + asize c₁) ⁻¹)))))) ⁻¹)
                                                                                 (annotate-bot e₂))
                                                                          (subst (λ z → unᵐ-β z ≤ q)
                                                                                 (if-false (reflects-false (<-reflects (1 + asize c₁ + asize c₂) (asize c₁))
                                                                                                           (≤→≯ $ ≤-suc-r ≤-+-r)) ⁻¹)
                                                                                 (has-bot q))))
                                                                  .snd .fst)
                                                 (↓-is-sup p₂ .least p₂'
                                                    λ where (b' , le) →
                                                               subst (_≤ p₂') (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c₁) (asize c₁)) refl))) $
                                                               ite-≤ⁱ-elim
                                                                 (subst (AnITE b bot
                                                                                 (annotate (shl (unᵐ-β ∘ single-at b' (1 + asize c₁)) 1) c₁)
                                                                                 (unᵐ-β (single-at b' (1 + asize c₁) (1 + asize c₁)))
                                                                                 (annotate (shl (unᵐ-β ∘ single-at b' (1 + asize c₁)) (2 + asize c₁)) c₂)
                                                                                 (unᵐ-β (single-at b' (1 + asize c₁) (2 + asize c₁ + asize c₂))) ≤ⁱ_) eq₀' $
                                                                  f ( single-at b' (1 + asize c₁)
                                                                    , ite-≤ⁱ-introl eq₀ (has-bot p₁)
                                                                        (subst (_≤ⁱ a₁)
                                                                               (annotate-ext λ n lt → ap unᵐ-β (if-false (reflects-false (==ⁿ-reflects (1 + asize c₁) (n + 1))
                                                                                                                            (contra (λ e → =→≤ (suc-inj (e ∙ +-comm n 1))) (<→≱ $ lt)))) ⁻¹)
                                                                               (annotate-bot e₁))
                                                                        (subst (_≤ p₂) (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c₁) (asize c₁)) refl)) ⁻¹) le)
                                                                        (subst (λ q → annotate q c₂ ≤ⁱ a₂)
                                                                               (shl-single-at-not {n = 1 + asize c₁} {m = 2 + asize c₁} (s<s <-ascend) ⁻¹)
                                                                               (annotate-bot e₂))
                                                                        (subst (λ z → unᵐ-β z ≤ q)
                                                                               (if-false (reflects-false (==ⁿ-reflects (asize c₁) (1 + asize c₁ + asize c₂))
                                                                                                         λ p → id≠plus-suc (p ∙ +-suc-r (asize c₁) (asize c₂) ⁻¹)) ⁻¹)
                                                                               (has-bot q))))
                                                                 .snd .snd .fst)
                                                 (ih₂ .is-basis.↓-is-sup (a₂ , e₂) .least (a₂' , e₂')
                                                     λ where (bf , le) →
                                                               subst (_≤ⁱ a₂') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₂)) lt)) $
                                                               subst (λ q → annotate q c₂ ≤ⁱ a₂')
                                                                     (shl-shr {f = filt bf (_<? asize c₂)} {n = 2 + asize c₁}) $
                                                               ite-≤ⁱ-elim
                                                                 (subst (AnITE b bot
                                                                          (annotate (shl (unᵐ-β ∘ shr (filt bf (_<? asize c₂)) (2 + asize c₁)) 1) c₁)
                                                                          (unᵐ-β (shr (filt bf (_<? asize c₂)) (2 + asize c₁) (1 + asize c₁)))
                                                                          (annotate (shl (unᵐ-β ∘ shr (filt bf (_<? asize c₂)) (2 + asize c₁)) (2 + asize c₁)) c₂)
                                                                          (unᵐ-β (shr (filt bf (_<? asize c₂)) (2 + asize c₁) (2 + asize c₁ + asize c₂))) ≤ⁱ_) eq₀' $
                                                                  f ( shr (filt bf (_<? asize c₂)) (2 + asize c₁)
                                                                    , ite-≤ⁱ-introl eq₀ (has-bot p₁)
                                                                         (subst (_≤ⁱ a₁)
                                                                                (annotate-ext λ n lt → ap unᵐ-β (if-false {b = 1 + asize c₁ <? n + 1}
                                                                                                                          (reflects-false (<-reflects (1 + asize c₁) (n + 1))
                                                                                                                                          (≤→≯ $ ≤ⁿ-trans (=→≤ (+-comm n 1)) (s≤s (<→≤ lt))))) ⁻¹)
                                                                                (annotate-bot e₁))
                                                                         (subst (λ z → unᵐ-β z ≤ p₂)
                                                                                (if-false (reflects-false (<-reflects (asize c₁) (asize c₁)) <-irr) ⁻¹)
                                                                                (has-bot p₂))
                                                                         (subst (λ q → annotate q c₂ ≤ⁱ a₂)
                                                                                (shl-shr {f = filt bf (_<? asize c₂)} {n = 2 + asize c₁} ⁻¹) $
                                                                          subst (_≤ⁱ a₂) (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₂)) lt) ⁻¹) le)
                                                                         (subst (λ z → unᵐ-β z ≤ q)
                                                                                (( if-true (reflects-true (<-reflects (asize c₁) (1 + asize c₁ + asize c₂))
                                                                                                          (<-+-r <-ascend))
                                                                                 ∙ if-false (reflects-false (<-reflects (asize c₁ + asize c₂ ∸ asize c₁) (asize c₂))
                                                                                                            (≤→≯ $ =→≤ (  +-cancel-∸-r (asize c₂) (asize c₁) ⁻¹
                                                                                                                        ∙ ap (_∸ asize c₁) (+-comm (asize c₂) (asize c₁)))))) ⁻¹)
                                                                                (has-bot q))))
                                                                 .snd .snd .snd .fst)
                                                 (↓-is-sup q .least q'
                                                    λ where (b' , le) →
                                                               subst (_≤ q')
                                                                     (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c₁ + asize c₂) (asize c₁ + asize c₂)) refl))) $
                                                               ite-≤ⁱ-elim
                                                                 (subst (AnITE b bot
                                                                                 (annotate (shl (unᵐ-β ∘ single-at b' (2 + asize c₁ + asize c₂)) 1) c₁)
                                                                                 (unᵐ-β (single-at b' (2 + asize c₁ + asize c₂) (1 + asize c₁)))
                                                                                 (annotate (shl (unᵐ-β ∘ single-at b' (2 + asize c₁ + asize c₂)) (2 + asize c₁)) c₂)
                                                                                 (unᵐ-β (single-at b' (2 + asize c₁ + asize c₂) (2 + asize c₁ + asize c₂))) ≤ⁱ_) eq₀' $
                                                                  f ( single-at b' (2 + asize c₁ + asize c₂)
                                                                    , ite-≤ⁱ-introl eq₀ (has-bot p₁)
                                                                         (subst (_≤ⁱ a₁)
                                                                                (annotate-ext λ n lt → ap unᵐ-β (if-false (reflects-false (==ⁿ-reflects (2 + asize c₁ + asize c₂) (n + 1))
                                                                                                                             (contra
                                                                                                                                (λ e → ≤-peel (≤ⁿ-trans (s≤s (≤-suc-r ≤-+-r))
                                                                                                                                                 (=→≤ (e ∙ +-comm n 1))))
                                                                                                                                (<→≱ $ lt)))) ⁻¹)
                                                                                (annotate-bot e₁))
                                                                         (subst (λ z → unᵐ-β z ≤ p₂)
                                                                                (if-false (reflects-false (==ⁿ-reflects (1 + asize c₁ + asize c₂) (asize c₁))
                                                                                                          λ e → id≠plus-suc ((+-suc-r (asize c₁) (asize c₂) ∙ e) ⁻¹)) ⁻¹)
                                                                                (has-bot p₂))
                                                                         (subst (_≤ⁱ a₂)
                                                                                (annotate-ext λ n lt → ap unᵐ-β (if-false (reflects-false (==ⁿ-reflects (2 + asize c₁ + asize c₂) (n + (2 + asize c₁)))
                                                                                                                             (contra
                                                                                                                                (λ e → =→≤ (+-cancel-r (asize c₂) n (2 + asize c₁)
                                                                                                                                               (+-comm (asize c₂) (2 + asize c₁) ∙ e)))
                                                                                                                                (<→≱ $ lt)))) ⁻¹)
                                                                                (annotate-bot e₂))
                                                                         (subst (_≤ q)
                                                                                (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c₁ + asize c₂) (asize c₁ + asize c₂)) refl)) ⁻¹)
                                                                                le)))
                                                                 .snd .snd .snd .snd)
                           }
    }
  anc-bas (While b c)   = {!!}
