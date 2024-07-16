module Nipkow.Collecting where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming (elim to elimᵇ)
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects renaming (dmap to dmapʳ)

open import List1
open import Nipkow.Lang

module Collsem
  (A : 𝒰)
  (sup : A → A → A)
  (leq : A → A → Bool)
  where

  open List1.List1

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

  _≤ⁱ_ : AnInstr A → AnInstr A → Bool
  c₁ ≤ⁱ c₂ = strip c₁ ==ⁱ strip c₂ and all2?₁ leq (annos c₁) (annos c₂)

  skip-≤ⁱ : ∀ {s c}
          → Reflects (Σ[ s' ꞉ A ] (c ＝ AnSkip s') × is-true (leq s s')) (AnSkip s ≤ⁱ c)
  skip-≤ⁱ {s} {c} = dmapʳ (λ where ((s' , eq) , le) →
                                       s' , eq , subst (is-true ∘ all2?₁ leq [ s ]₁ ∘ annos) eq le)
                          (_∘ λ where (s' , eq , le) →
                                        (s' , eq) , subst (is-true ∘ all2?₁ leq [ s ]₁ ∘ annos) (eq ⁻¹) le)
                          (reflects-and2 (reflects-strip-skip c) reflects-id)

  assign-≤ⁱ : ∀ {x e s c}
            → Reflects (Σ[ s' ꞉ A ] (c ＝ AnAssign x e s') × is-true (leq s s')) (AnAssign x e s ≤ⁱ c)
  assign-≤ⁱ {s} {c} = dmapʳ (λ where ((s' , eq) , le) →
                                         s' , eq , subst (is-true ∘ all2?₁ leq [ s ]₁ ∘ annos) eq le)
                            (_∘ λ where (s' , eq , le) →
                                          (s' , eq) , subst (is-true ∘ all2?₁ leq [ s ]₁ ∘ annos) (eq ⁻¹) le)
                            (reflects-and2 (reflects-strip-assign c) reflects-id)

  seq-≤ⁱ : ∀ {c₁ c₂ c}
         → Reflects (Σ[ c₃ ꞉ AnInstr A ] Σ[ c₄ ꞉ AnInstr A ]
                           (c ＝ AnSeq c₃ c₄)
                         × is-true (c₁ ≤ⁱ c₃) × is-true (c₂ ≤ⁱ c₄))
                    (AnSeq c₁ c₂ ≤ⁱ c)
  seq-≤ⁱ {c₁} {c₂} {c} =
    dmapʳ (λ where ((a₁ , a₂ , eq₁ , eq₂ , eq₃) , le) →
                       let eq1' = reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₂ ⁻¹)
                           eq2' = reflects-true (reflects-instr (strip c₂) (strip a₂)) (eq₃ ⁻¹)
                           le12 = and-true-≃ {x = all2?₁ leq (annos c₁) (annos a₁)} {y = all2?₁ leq (annos c₂) (annos a₂)} $
                                  subst is-true (all2?-++₁ (length-annos-same {c₁ = c₁} eq1')) $
                                  subst (is-true ∘ all2?₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) eq₁ le
                        in
                          a₁ , a₂ , eq₁
                        , (and-true-≃ {x = strip c₁ ==ⁱ strip a₁} {y = all2?₁ leq (annos c₁) (annos a₁)} ⁻¹ $ eq1' , le12 .fst)
                        , (and-true-≃ {x = strip c₂ ==ⁱ strip a₂} {y = all2?₁ leq (annos c₂) (annos a₂)} ⁻¹ $ eq2' , le12 .snd))
          (_∘ λ where (c₃ , c₄ , eq , le₁ , le₂) →
                        let le1' = and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = all2?₁ leq (annos c₁) (annos c₃)} $ le₁
                            le2' = and-true-≃ {x = strip c₂ ==ⁱ strip c₄} {y = all2?₁ leq (annos c₂) (annos c₄)} $ le₂
                          in
                          ( ( c₃ , c₄ , eq
                            , true-reflects (reflects-instr (strip c₁) (strip c₃)) (le1' .fst) ⁻¹
                            , true-reflects (reflects-instr (strip c₂) (strip c₄)) (le2' .fst) ⁻¹))
                          , subst (is-true ∘ all2?₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) (eq ⁻¹)
                                  (subst is-true
                                    (all2?-++₁ (length-annos-same {c₁ = c₁} {c₂ = c₃} (le1' .fst)) ⁻¹)
                                    (and-true-≃ {x = all2?₁ leq (annos c₁) (annos c₃)} {y = all2?₁ leq (annos c₂) (annos c₄)} ⁻¹ $
                                     le1' .snd , le2' .snd)))
          (reflects-and2 (reflects-strip-seq c) reflects-id)

  mono-post : ∀ {c₁ c₂} → is-true (c₁ ≤ⁱ c₂) → is-true (leq (post c₁) (post c₂))
  mono-post {c₁} {c₂} c =
    (and-true-≃ {x = all id (zip-with leq (annos c₁ .init) (annos c₂ .init))}
                {y = leq (annos c₁ .last) (annos c₂ .last)} $
       (and-true-≃ {x = strip c₁ ==ⁱ strip c₂} {y = all2?₁ leq (annos c₁) (annos c₂)} $ c) .snd) .snd

