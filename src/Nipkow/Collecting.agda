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
                          , (subst (is-true ∘ all2?₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) (eq ⁻¹) $
                             subst is-true (all2?-++₁ (length-annos-same {c₁ = c₁} {c₂ = c₃} (le1' .fst)) ⁻¹) $
                             and-true-≃ {x = all2?₁ leq (annos c₁) (annos c₃)} {y = all2?₁ leq (annos c₂) (annos c₄)} ⁻¹ $
                             le1' .snd , le2' .snd))
          (reflects-and2 (reflects-strip-seq c) reflects-id)

  ite-≤ⁱ : ∀ {b p₁ c₁ p₂ c₂ q₁ c}
         → Reflects (Σ[ p₃ ꞉ A ] Σ[ c₃ ꞉ AnInstr A ] Σ[ p₄ ꞉ A ] Σ[ c₄ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                          (c ＝ AnITE b p₃ c₃ p₄ c₄ q₂)
                        × is-true (leq p₁ p₃) × is-true (c₁ ≤ⁱ c₃)
                        × is-true (leq p₂ p₄) × is-true (c₂ ≤ⁱ c₄)
                        × is-true (leq q₁ q₂))
                    (AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c)
  ite-≤ⁱ {p₁} {c₁} {p₂} {c₂} {q₁} {c} =
    dmapʳ (λ where ((p₃ , c₃ , p₄ , c₄ , q₂ , eq₁ , eq₂ , eq₃) , le) →
                      let eq1' = reflects-true (reflects-instr (strip c₁) (strip c₃)) (eq₂ ⁻¹)
                          eq2' = reflects-true (reflects-instr (strip c₂) (strip c₄)) (eq₃ ⁻¹)
                          le1 = and-true-≃ {x = all2?₁ leq ((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂))
                                                           ((p₃ ∷₁ annos c₃) ++₁ (p₄ ∷₁ annos c₄))}
                                           {y = leq q₁ q₂} $
                                subst is-true (all2?-∶+₁ {p = leq}
                                                         (  length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
                                                          ∙ ap² _+_ (ap suc (length-annos-same {c₁ = c₁} eq1')) (ap suc (length-annos-same {c₁ = c₂} eq2'))
                                                          ∙ length₁-++ {xs = p₃ ∷₁ annos c₃} {ys = p₄ ∷₁ annos c₄} ⁻¹)) $
                                subst (is-true ∘ all2?₁ leq (((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₁) ∘ annos) eq₁ le
                          le2 = and-true-≃ {x = all2?₁ leq (p₁ ∷₁ annos c₁) (p₃ ∷₁ annos c₃)}
                                            {y = all2?₁ leq (p₂ ∷₁ annos c₂) (p₄ ∷₁ annos c₄)} $
                                 subst is-true (all2?-++₁ {p = leq} (ap suc (length-annos-same {c₁ = c₁} {c₂ = c₃} eq1'))) (le1 .fst)
                          le3 = and-true-≃ {x = leq p₁ p₃} {y = all2?₁ leq (annos c₁) (annos c₃)} $
                                subst is-true (all2?-∶∶₁ {p = leq} {xs = annos c₁}) (le2 .fst)
                          le4 = and-true-≃ {x = leq p₂ p₄} {y = all2?₁ leq (annos c₂) (annos c₄)} $
                                subst is-true (all2?-∶∶₁ {p = leq} {xs = annos c₂}) (le2 .snd)
                        in
                        p₃ , c₃ , p₄ , c₄ , q₂ , eq₁
                      , le3 .fst
                      , (and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = all2?₁ leq (annos c₁) (annos c₃)} ⁻¹ $ eq1' , le3 .snd)
                      , le4 .fst
                      , (and-true-≃ {x = strip c₂ ==ⁱ strip c₄} {y = all2?₁ leq (annos c₂) (annos c₄)} ⁻¹ $ eq2' , le4. snd)
                      , le1 .snd)
          (_∘ λ where (p₃ , c₃ , p₄ , c₄ , q₂ , eq , le₁ , le₂ , le₃ , le₄ , le₅) →
                        let le2' = and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = all2?₁ leq (annos c₁) (annos c₃)} $ le₂
                            le4' = and-true-≃ {x = strip c₂ ==ⁱ strip c₄} {y = all2?₁ leq (annos c₂) (annos c₄)} $ le₄
                         in
                          ( p₃ , c₃ , p₄ , c₄ , q₂ , eq
                          , true-reflects (reflects-instr (strip c₁) (strip c₃)) (le2' .fst) ⁻¹
                          , true-reflects (reflects-instr (strip c₂) (strip c₄)) (le4' .fst) ⁻¹)
                        , (subst (is-true ∘ all2?₁ leq (((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₁) ∘ annos) (eq ⁻¹) $
                           subst is-true (all2?-∶+₁ {p = leq} (length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
                                                          ∙ ap² _+_ (ap suc (length-annos-same {c₁ = c₁} (le2' .fst)))
                                                                    (ap suc (length-annos-same {c₁ = c₂} (le4' .fst)))
                                                          ∙ length₁-++ {xs = p₃ ∷₁ annos c₃} {ys = p₄ ∷₁ annos c₄} ⁻¹) ⁻¹) $
                           and-true-≃ {x = all2?₁ leq ((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂))
                                                           ((p₃ ∷₁ annos c₃) ++₁ (p₄ ∷₁ annos c₄))}
                                           {y = leq q₁ q₂} ⁻¹ $
                             (subst is-true (all2?-++₁ {p = leq} (ap suc (length-annos-same {c₁ = c₁} {c₂ = c₃} (le2' .fst))) ⁻¹) $
                              and-true-≃ {x = all2?₁ leq (p₁ ∷₁ annos c₁) (p₃ ∷₁ annos c₃)}
                                         {y = all2?₁ leq (p₂ ∷₁ annos c₂) (p₄ ∷₁ annos c₄)} ⁻¹ $
                                (subst is-true (all2?-∶∶₁ {p = leq} {xs = annos c₁} ⁻¹) $
                                 and-true-≃ {x = leq p₁ p₃} {y = all2?₁ leq (annos c₁) (annos c₃)} ⁻¹ $
                                 le₁ , le2' .snd)
                              , (subst is-true (all2?-∶∶₁ {p = leq} {xs = annos c₂} ⁻¹) $
                                 and-true-≃ {x = leq p₂ p₄} {y = all2?₁ leq (annos c₂) (annos c₄)} ⁻¹ $
                                 le₃ , le4' .snd))
                           , le₅))
          (reflects-and2 (reflects-strip-ite c) reflects-id)

  mono-post : ∀ {c₁ c₂} → is-true (c₁ ≤ⁱ c₂) → is-true (leq (post c₁) (post c₂))
  mono-post {c₁} {c₂} c =
    (and-true-≃ {x = all id (zip-with leq (annos c₁ .init) (annos c₂ .init))}
                {y = leq (annos c₁ .last) (annos c₂ .last)} $
       (and-true-≃ {x = strip c₁ ==ⁱ strip c₂} {y = all2?₁ leq (annos c₁) (annos c₂)} $ c) .snd) .snd

