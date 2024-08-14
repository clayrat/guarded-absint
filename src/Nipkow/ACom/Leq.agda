module Nipkow.ACom.Leq where

open import Prelude
open import Data.String
open import Data.List
open import Data.List.Correspondences.Binary.All
open import Data.Reflects

open import List1
open import Nipkow.Lang
open import Nipkow.ACom

module AnInstrLeq
    (A : 𝒰 (ℓsuc 0ℓ))
    (leq : A → A → 𝒰)
  where

  open List1.List1

  data _≤ⁱ_ : AnInstr A → AnInstr A → 𝒰 (ℓsuc 0ℓ) where
    Skip-≤ⁱ : ∀ {a₁ a₂}
            → leq a₁ a₂
            → AnSkip a₁ ≤ⁱ AnSkip a₂

    Assign-≤ⁱ : ∀ {x₁ e₁ a₁ x₂ e₂ a₂}
              → x₁ ＝ x₂
              → e₁ ＝ e₂
              → leq a₁ a₂
              → AnAssign x₁ e₁ a₁ ≤ⁱ AnAssign x₂ e₂ a₂

    Seq-≤ⁱ : ∀ {c₁ c₂ c₃ c₄}
           → c₁ ≤ⁱ c₃
           → c₂ ≤ⁱ c₄
           → AnSeq c₁ c₂ ≤ⁱ AnSeq c₃ c₄

    ITE-≤ⁱ : ∀ {b₁ p₁ c₁ p₂ c₂ q₁ b₂ p₃ c₃ p₄ c₄ q₂}
           → b₁ ＝ b₂
           → leq p₁ p₃
           → c₁ ≤ⁱ c₃
           → leq p₂ p₄
           → c₂ ≤ⁱ c₄
           → leq q₁ q₂
           → AnITE b₁ p₁ c₁ p₂ c₂ q₁ ≤ⁱ AnITE b₂ p₃ c₃ p₄ c₄ q₂

    While-≤ⁱ : ∀ {inv₁ b₁ p₁ c₁ q₁ inv₂ b₂ p₂ c₂ q₂}
             → leq inv₁ inv₂
             → b₁ ＝ b₂
             → leq p₁ p₂
             → c₁ ≤ⁱ c₂
             → leq q₁ q₂
             → AnWhile inv₁ b₁ p₁ c₁ q₁ ≤ⁱ AnWhile inv₂ b₂ p₂ c₂ q₂

  -- structural helpers
  opaque

    -- Skip

    skip-≤ⁱ-intro2 : ∀ {c₁ c₂ a₁ a₂}
                    → c₁ ＝ AnSkip a₁
                    → c₂ ＝ AnSkip a₂
                    → leq a₁ a₂
                    → c₁ ≤ⁱ c₂
    skip-≤ⁱ-intro2 {c₂} {a₁} eq₁ eq₂ le =
      subst (_≤ⁱ c₂) (eq₁ ⁻¹) $
      subst (AnSkip a₁ ≤ⁱ_) (eq₂ ⁻¹) (Skip-≤ⁱ le)

    skip-≤ⁱ-eliml : ∀ {a₁ c}
                  → AnSkip a₁ ≤ⁱ c
                  → Σ[ a₂ ꞉ A ] (c ＝ AnSkip a₂) × leq a₁ a₂
    skip-≤ⁱ-eliml (Skip-≤ⁱ {a₂} le) = a₂ , refl , le

    skip-≤ⁱ-elim : ∀ {s s'}
                 → AnSkip s ≤ⁱ AnSkip s'
                 → leq s s'
    skip-≤ⁱ-elim (Skip-≤ⁱ le) = le

    skip-≤ⁱ-elim2 : ∀ {c₁ c₂ a₁ a₂}
                    → c₁ ＝ AnSkip a₁
                    → c₂ ＝ AnSkip a₂
                    → c₁ ≤ⁱ c₂
                    → leq a₁ a₂
    skip-≤ⁱ-elim2 {c₁} {a₂} e₁ e₂ le =
      skip-≤ⁱ-elim $
      subst (_≤ⁱ AnSkip a₂) e₁ $
      subst (c₁ ≤ⁱ_) e₂ le

    -- Assign

    assign-≤ⁱ-intro2 : ∀ {c₁ c₂ x e a₁ a₂}
                     → c₁ ＝ AnAssign x e a₁
                     → c₂ ＝ AnAssign x e a₂
                     → leq a₁ a₂
                     → c₁ ≤ⁱ c₂
    assign-≤ⁱ-intro2 {c₂} {x} {e} {a₁} eq₁ eq₂ le =
      subst (_≤ⁱ c₂) (eq₁ ⁻¹) $
      subst (AnAssign x e a₁ ≤ⁱ_) (eq₂ ⁻¹) $
      Assign-≤ⁱ refl refl le

    assign-≤ⁱ-eliml : ∀ {x e a₁ c}
                    → AnAssign x e a₁ ≤ⁱ c
                    → Σ[ a₂ ꞉ A ] (c ＝ AnAssign x e a₂) × leq a₁ a₂
    assign-≤ⁱ-eliml (Assign-≤ⁱ {a₂} e₁ e₂ le) = a₂ , ap² (λ x y → AnAssign x y a₂) (e₁ ⁻¹) (e₂ ⁻¹) , le

    assign-≤ⁱ-elim : ∀ {x e s s'}
                   → AnAssign x e s ≤ⁱ AnAssign x e s'
                   → leq s s'
    assign-≤ⁱ-elim {s} p =
      let (s' , e , le) = assign-≤ⁱ-eliml p in
      subst (leq s) (AnAssign-inj e .snd .snd ⁻¹) le

    assign-≤ⁱ-elim2 : ∀ {c₁ c₂ x e a₁ a₂}
                     → c₁ ＝ AnAssign x e a₁
                     → c₂ ＝ AnAssign x e a₂
                     → c₁ ≤ⁱ c₂
                     → leq a₁ a₂
    assign-≤ⁱ-elim2 {c₁} {x} {e} {a₂} e₁ e₂ le =
      assign-≤ⁱ-elim $
      subst (_≤ⁱ AnAssign x e a₂) e₁ $
      subst (c₁ ≤ⁱ_) e₂ le

    -- Seq

    seq-≤ⁱ-intro2 : ∀ {c₁ c₂ c₁₁ c₂₁ c₁₂ c₂₂}
                  → c₁ ＝ AnSeq c₁₁ c₂₁
                  → c₂ ＝ AnSeq c₁₂ c₂₂
                  → c₁₁ ≤ⁱ c₁₂
                  → c₂₁ ≤ⁱ c₂₂
                  → c₁ ≤ⁱ c₂
    seq-≤ⁱ-intro2 {c₂} {c₁₁} {c₂₁} eq₁ eq₂ le₁ le₂ =
        subst (_≤ⁱ c₂) (eq₁ ⁻¹) $
        subst (AnSeq c₁₁ c₂₁ ≤ⁱ_) (eq₂ ⁻¹) $
        Seq-≤ⁱ le₁ le₂

    seq-≤ⁱ-eliml : ∀ {c₁ c₂ c}
             → AnSeq c₁ c₂ ≤ⁱ c
             → Σ[ c₃ ꞉ AnInstr A ] Σ[ c₄ ꞉ AnInstr A ]
                 (c ＝ AnSeq c₃ c₄) × c₁ ≤ⁱ c₃ × c₂ ≤ⁱ c₄
    seq-≤ⁱ-eliml (Seq-≤ⁱ {c₃} {c₄} le₁ le₂) = c₃ , c₄ , refl , le₁ , le₂

    seq-≤ⁱ-elim : ∀ {c₁ c₂ c₃ c₄}
                → AnSeq c₁ c₂ ≤ⁱ AnSeq c₃ c₄
                → c₁ ≤ⁱ c₃ × c₂ ≤ⁱ c₄
    seq-≤ⁱ-elim {c₁} {c₂} le =
      let (c₃ , c₄ , e , le₁ , le₂) = seq-≤ⁱ-eliml le
          (e₁ , e₂) = AnSeq-inj e
        in
        subst (c₁ ≤ⁱ_) (e₁ ⁻¹) le₁
      , subst (c₂ ≤ⁱ_) (e₂ ⁻¹) le₂

    seq-≤ⁱ-elim2 : ∀ {c₁ c₂ c₁₁ c₂₁ c₁₂ c₂₂}
                 → c₁ ＝ AnSeq c₁₁ c₂₁
                 → c₂ ＝ AnSeq c₁₂ c₂₂
                 → c₁ ≤ⁱ c₂
                 → c₁₁ ≤ⁱ c₁₂ × c₂₁ ≤ⁱ c₂₂
    seq-≤ⁱ-elim2 {c₁} {c₁₂} {c₂₂} e₁ e₂ le =
      seq-≤ⁱ-elim $
      subst (_≤ⁱ AnSeq c₁₂ c₂₂) e₁ $
      subst (c₁ ≤ⁱ_) e₂ le

    -- ITE

    ite-≤ⁱ-intro2 : ∀ {b c₁ p₁₁ c₁₁ p₂₁ c₂₁ q₁ c₂ p₁₂ c₁₂ p₂₂ c₂₂ q₂}
                  → c₁ ＝ AnITE b p₁₁ c₁₁ p₂₁ c₂₁ q₁
                  → c₂ ＝ AnITE b p₁₂ c₁₂ p₂₂ c₂₂ q₂
                  → leq p₁₁ p₁₂
                  → c₁₁ ≤ⁱ c₁₂
                  → leq p₂₁ p₂₂
                  → c₂₁ ≤ⁱ c₂₂
                  → leq q₁ q₂
                  → c₁ ≤ⁱ c₂
    ite-≤ⁱ-intro2 {b} {p₁₁} {c₁₁} {p₂₁} {c₂₁} {q₁} {c₂} eq₁ eq₂ le₁ le₂ le₃ le₄ le₅ =
      subst (_≤ⁱ c₂) (eq₁ ⁻¹) $
      subst (AnITE b p₁₁ c₁₁ p₂₁ c₂₁ q₁ ≤ⁱ_) (eq₂ ⁻¹) $
      ITE-≤ⁱ refl le₁ le₂ le₃ le₄ le₅

    ite-≤ⁱ-eliml : ∀ {b p₁ c₁ p₂ c₂ q₁ c}
                 → AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c
                 → Σ[ p₃ ꞉ A ] Σ[ c₃ ꞉ AnInstr A ] Σ[ p₄ ꞉ A ] Σ[ c₄ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                                  (c ＝ AnITE b p₃ c₃ p₄ c₄ q₂)
                                × leq p₁ p₃ × c₁ ≤ⁱ c₃ × leq p₂ p₄ × c₂ ≤ⁱ c₄ × leq q₁ q₂
    ite-≤ⁱ-eliml (ITE-≤ⁱ {p₃} {c₃} {p₄} {c₄} {q₂} e le₁ le₂ le₃ le₄ le₅) =
      p₃ , c₃ , p₄ , c₄ , q₂ , ap (λ x → AnITE x p₃ c₃ p₄ c₄ q₂) (e ⁻¹) , le₁ , le₂ , le₃ , le₄ , le₅

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

    ite-≤ⁱ-elim2 : ∀ {b c₁ p₁₁ c₁₁ p₂₁ c₂₁ q₁ c₂ p₁₂ c₁₂ p₂₂ c₂₂ q₂}
                 → c₁ ＝ AnITE b p₁₁ c₁₁ p₂₁ c₂₁ q₁
                 → c₂ ＝ AnITE b p₁₂ c₁₂ p₂₂ c₂₂ q₂
                 → c₁ ≤ⁱ c₂
                 → leq p₁₁ p₁₂ × c₁₁ ≤ⁱ c₁₂ × leq p₂₁ p₂₂ × c₂₁ ≤ⁱ c₂₂ × leq q₁ q₂
    ite-≤ⁱ-elim2 {b} {c₁} {p₁₂} {c₁₂} {p₂₂} {c₂₂} {q₂} e₁ e₂ le =
      ite-≤ⁱ-elim $
      subst (_≤ⁱ AnITE b p₁₂ c₁₂ p₂₂ c₂₂ q₂) e₁ $
      subst (c₁ ≤ⁱ_) e₂ le

    -- While

    while-≤ⁱ-intro2 : ∀ {c₁ c₂ b inv₁ p₁ c₁₁ q₁ inv₂ p₂ c₂₂ q₂}
                    → c₁ ＝ AnWhile inv₁ b p₁ c₁₁ q₁
                    → c₂ ＝ AnWhile inv₂ b p₂ c₂₂ q₂
                    → leq inv₁ inv₂
                    → leq p₁ p₂
                    → c₁₁ ≤ⁱ c₂₂
                    → leq q₁ q₂
                    → c₁ ≤ⁱ c₂
    while-≤ⁱ-intro2 {c₂} {b} {inv₁} {p₁} {c₁₁} {q₁} eq₁ eq₂ le₁ le₂ le₃ le₄ =
      subst (_≤ⁱ c₂) (eq₁ ⁻¹) $
      subst (AnWhile inv₁ b p₁ c₁₁ q₁ ≤ⁱ_) (eq₂ ⁻¹) $
      While-≤ⁱ le₁ refl le₂ le₃ le₄

    while-≤ⁱ-eliml : ∀ {inv₁ b p₁ c₁ q₁ c}
                   → AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ c
                   → Σ[ inv₂ ꞉ A ] Σ[ p₂ ꞉ A ] Σ[ c₂ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                         (c ＝ AnWhile inv₂ b p₂ c₂ q₂)
                       × leq inv₁ inv₂ × leq p₁ p₂ × c₁ ≤ⁱ c₂ × leq q₁ q₂
    while-≤ⁱ-eliml (While-≤ⁱ {inv₂} {p₂} {c₂} {q₂} le₁ e le₂ le₃ le₄) =
      inv₂ , p₂ , c₂ , q₂ , ap (λ x → AnWhile inv₂ x p₂ c₂ q₂) (e ⁻¹) , le₁ , le₂ , le₃ , le₄

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

    while-≤ⁱ-elim2 : ∀ {c₁ c₂ b inv₁ p₁ c₁₁ q₁ inv₂ p₂ c₂₂ q₂}
                    → c₁ ＝ AnWhile inv₁ b p₁ c₁₁ q₁
                    → c₂ ＝ AnWhile inv₂ b p₂ c₂₂ q₂
                    → c₁ ≤ⁱ c₂
                    → leq inv₁ inv₂ × leq p₁ p₂ × c₁₁ ≤ⁱ c₂₂ × leq q₁ q₂
    while-≤ⁱ-elim2 {c₁} {b} {inv₂} {p₂} {c₂₂} {q₂} e₁ e₂ le =
      while-≤ⁱ-elim $
      subst (_≤ⁱ AnWhile inv₂ b p₂ c₂₂ q₂) e₁ $
      subst (c₁ ≤ⁱ_) e₂ le

  -- conversion to strip + all2

  ≤ⁱ→=all : ∀ {c₁ c₂} → c₁ ≤ⁱ c₂ → (strip c₁ ＝ strip c₂) × All²₁ leq (annos c₁) (annos c₂)
  ≤ⁱ→=all (Skip-≤ⁱ le)                   =
    refl , [] , le
  ≤ⁱ→=all (Assign-≤ⁱ e₁ e₂ le)           =
    ap² Assign e₁ e₂ , [] , le
  ≤ⁱ→=all (Seq-≤ⁱ le₁ le₂)               =
    let (e₁ , a₁) = ≤ⁱ→=all le₁
        (e₂ , a₂) = ≤ⁱ→=all le₂
       in
    ap² Seq e₁ e₂ , All²₁-++₁ a₁ a₂
  ≤ⁱ→=all (ITE-≤ⁱ {b₁} {c₁} {c₂} {b₂} {c₃} {c₄} e le₁ le₂ le₃ le₄ le₅) =
    let (e₁ , a₁) = ≤ⁱ→=all le₂
        (e₂ , a₂) = ≤ⁱ→=all le₄
       in
      ap² (λ x y → ITE x y (strip c₂)) e e₁ ∙ ap (ITE b₂ (strip c₃)) e₂
    , All²₁-∶+₁-r (All²₁-++₁ (All²-∶∶₁-r le₁ a₁) (All²-∶∶₁-r le₃ a₂)) le₅
  ≤ⁱ→=all (While-≤ⁱ le₁ e le₂ le₃ le₄)   =
    let (e₁ , a₁) = ≤ⁱ→=all le₃ in
      ap² While e e₁
    , All²₁-∶+₁-r (All²-∶∶₁-r le₁ (All²-∶∶₁-r le₂ a₁)) le₄

  =all→≤ⁱ : ∀ {c₁ c₂} → strip c₁ ＝ strip c₂ → All²₁ leq (annos c₁) (annos c₂) → c₁ ≤ⁱ c₂
  =all→≤ⁱ {c₁} {c₂ = AnSkip a₂}                   e a =
    let (a₁ , e₁) = strip-skip-r e
        (_ , le) = subst (λ x → All²₁ leq (annos x) [ a₂ ]₁) e₁ a
      in
    skip-≤ⁱ-intro2 e₁ refl le
  =all→≤ⁱ {c₁} {c₂ = AnAssign x₂ e₂ a₂}           e a =
    let (a₁ , e₁) = strip-assign-r e
        (_ , le) = subst (λ x → All²₁ leq (annos x) [ a₂ ]₁) e₁ a
      in
    assign-≤ⁱ-intro2 e₁ refl le
  =all→≤ⁱ {c₁} {c₂ = AnSeq c₁₂ c₂₂}               e a =
    let (a₁ , a₂ , e₁ , e₂ , e₃) = strip-seq-r e
        (le₁ , le₂) = All²₁-split
                        (length-annos-same {c₁ = a₁}
                           (reflects-true (reflects-instr (strip a₁) (strip c₁₂)) e₂))
                        (subst (λ x → All²₁ leq (annos x) (annos c₁₂ ++₁ annos c₂₂)) e₁ a)
      in
    seq-≤ⁱ-intro2 e₁ refl (=all→≤ⁱ e₂ le₁) (=all→≤ⁱ e₃ le₂)
  =all→≤ⁱ {c₁} {c₂ = AnITE b₂ p₁₂ c₁₂ p₂₂ c₂₂ q₂} e a =
    let (p₃ , a₁ , p₄ , a₂ , q , e₀ , e₁ , e₂) = strip-ite-r e
        lp₁ = length-annos-same {c₁ = a₁} $ reflects-true (reflects-instr (strip a₁) (strip c₁₂)) e₁
        le = All²₁-∶+₁-l (  length₁-++ {xs = p₃ ∷₁ annos a₁} {ys = p₄ ∷₁ annos a₂}
                         ∙ ap² (λ x y → suc x + suc y) lp₁
                               (length-annos-same {c₁ = a₂}
                                  (reflects-true (reflects-instr (strip a₂) (strip c₂₂)) e₂))
                         ∙ length₁-++ {xs = p₁₂ ∷₁ annos c₁₂} {ys = p₂₂ ∷₁ annos c₂₂} ⁻¹) $
             subst (λ x → All²₁ leq (annos x) (((p₁₂ ∷₁ annos c₁₂) ++₁ (p₂₂ ∷₁ annos c₂₂)) ∶+₁ q₂)) e₀ a
        (le₁₁ , le₁₂) = All²₁-split (ap suc lp₁) (le .fst)
        (le₂₁ , le₂₂) = All²-∶∶₁-l le₁₁
        (le₃₁ , le₃₂) = All²-∶∶₁-l le₁₂
      in
    ite-≤ⁱ-intro2 e₀ refl le₂₁ (=all→≤ⁱ e₁ le₂₂) le₃₁ (=all→≤ⁱ e₂ le₃₂) (le .snd)
  =all→≤ⁱ {c₁} {c₂ = AnWhile inv₂ b₂ p₂ c₂ q₂}    e a =
    let (inv₁ , p₁ , a₁ , q₁ , e₀ , e₁) = strip-while-r e
        le = All²₁-∶+₁-l (ap (2 +_)
                            (length-annos-same {c₁ = a₁}
                              (reflects-true (reflects-instr (strip a₁) (strip c₂)) e₁))) $
             subst (λ x → All²₁ leq (annos x) (((inv₂ ∷₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₂))) e₀ a
        (le₁₁ , le₁₂) = All²-∶∶₁-l (le .fst)
        (le₂₁ , le₂₂) = All²-∶∶₁-l le₁₂
      in
    while-≤ⁱ-intro2 e₀ refl le₁₁ le₂₁ (=all→≤ⁱ e₁ le₂₂) (le .snd)

  -- postcondition monotonicity

  mono-post : ∀ {c₁ c₂} → c₁ ≤ⁱ c₂ → leq (post c₁) (post c₂)
  mono-post = snd ∘ snd ∘ ≤ⁱ→=all

module AnInstrLeqProp
    (A : 𝒰 (ℓsuc 0ℓ))
    (leq : A → A → 𝒰)
    (leq-prop : ∀ {a b} → is-prop (leq a b))
    (leq-refl : ∀ {x} → leq x x)
    (leq-trans : ∀ {x y z} → leq x y → leq y z → leq x z)
    (leq-antisym : ∀ {x y} → leq x y → leq y x → x ＝ y)
  where

  open List1.List1
  open AnInstrLeq A leq

  -- thinness

  ≤ⁱ-prop : ∀ {c₁ c₂} → is-prop (c₁ ≤ⁱ c₂)
  ≤ⁱ-prop (Skip-≤ⁱ le₁)                        (Skip-≤ⁱ le₂)                        =
    ap Skip-≤ⁱ (leq-prop le₁ le₂)
  ≤ⁱ-prop (Assign-≤ⁱ {x₁} {x₂} p₁₁ p₂₁ le₁)    (Assign-≤ⁱ p₁₂ p₂₂ le₂)              =
      ap² (λ x y → Assign-≤ⁱ x y le₁) (is-discrete→is-set auto x₁ x₂ p₁₁ p₁₂) (hlevel 1 p₂₁ p₂₂)
    ∙ ap (Assign-≤ⁱ p₁₂ p₂₂) (leq-prop le₁ le₂)
  ≤ⁱ-prop (Seq-≤ⁱ le₁₁ le₂₁)                   (Seq-≤ⁱ le₁₂ le₂₂)                   =
    ap² Seq-≤ⁱ (≤ⁱ-prop le₁₁ le₁₂) (≤ⁱ-prop le₂₁ le₂₂)
  ≤ⁱ-prop (ITE-≤ⁱ e₁ le₁₁ le₂₁ le₃₁ le₄₁ le₅₁) (ITE-≤ⁱ e₂ le₁₂ le₂₂ le₃₂ le₄₂ le₅₂) =
      ap² (λ x y → ITE-≤ⁱ x y le₂₁ le₃₁ le₄₁ le₅₁) (hlevel 1 e₁ e₂) (leq-prop le₁₁ le₁₂)
    ∙ ap² (λ x y → ITE-≤ⁱ e₂ le₁₂ x y le₄₁ le₅₁) (≤ⁱ-prop le₂₁ le₂₂) (leq-prop le₃₁ le₃₂)
    ∙ ap² (ITE-≤ⁱ e₂ le₁₂ le₂₂ le₃₂) (≤ⁱ-prop le₄₁ le₄₂) (leq-prop le₅₁ le₅₂)
  ≤ⁱ-prop (While-≤ⁱ le₁₁ e₁ le₂₁ le₃₁ le₄₁)    (While-≤ⁱ le₁₂ e₂ le₂₂ le₃₂ le₄₂)   =
      ap² (λ x y → While-≤ⁱ x y le₂₁ le₃₁ le₄₁) (leq-prop le₁₁ le₁₂) (hlevel 1 e₁ e₂)
    ∙ ap² (λ x y → While-≤ⁱ le₁₂ e₂ x y le₄₁) (leq-prop le₂₁ le₂₂) (≤ⁱ-prop le₃₁ le₃₂)
    ∙ ap (While-≤ⁱ le₁₂ e₂ le₂₂ le₃₂) (leq-prop le₄₁ le₄₂)

  instance
    H-Level-≤ⁱ : ∀ {n c₁ c₂} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (c₁ ≤ⁱ c₂)
    H-Level-≤ⁱ ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 ≤ⁱ-prop
    {-# OVERLAPPING H-Level-≤ⁱ #-}

  -- equivalence to strip + all2

  ≤ⁱ≃=all : ∀ {c₁ c₂} → c₁ ≤ⁱ c₂ ≃ (strip c₁ ＝ strip c₂) × All²₁ leq (annos c₁) (annos c₂)
  ≤ⁱ≃=all = prop-extₑ ≤ⁱ-prop (×-is-of-hlevel 1 (hlevel 1)
                                             (All²₁-is-of-hlevel 0 (λ _ _ → leq-prop)))
                     ≤ⁱ→=all λ p → =all→≤ⁱ (p .fst) (p .snd)

  -- partial order properties

  ≤ⁱ-refl : ∀ {x} → x ≤ⁱ x
  ≤ⁱ-refl = =all→≤ⁱ refl (all²₁-refl λ _ → leq-refl)

  ≤ⁱ-trans : ∀ {x y z} → x ≤ⁱ y → y ≤ⁱ z → x ≤ⁱ z
  ≤ⁱ-trans lxy lyz =
    let (exy , axy) = ≤ⁱ→=all lxy
        (eyz , ayz) = ≤ⁱ→=all lyz
      in
    =all→≤ⁱ (exy ∙ eyz) (all²₁-trans (λ _ _ _ → leq-trans) axy ayz)

  ≤ⁱ-antisym : ∀ {x y} → x ≤ⁱ y → y ≤ⁱ x → x ＝ y
  ≤ⁱ-antisym lxy lyx =
    let (exy , axy) = ≤ⁱ→=all lxy
        (eyx , ayx) = ≤ⁱ→=all lyx
      in
    strip-annos-same (reflects-true (reflects-instr (strip _) (strip _)) exy)
                     (all²₁-antisym (λ _ _ → leq-antisym) axy ayx)
