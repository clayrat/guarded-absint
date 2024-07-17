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
  (leq-sup-r1 : ∀ {x a b} → is-true (leq x a) → is-true (leq x (sup a b)))
  (leq-sup-r2 : ∀ {x a b} → is-true (leq x b) → is-true (leq x (sup a b)))
  (leq-sup-l : ∀ {x a b} → is-true (leq a x) → is-true (leq b x) → is-true (leq (sup a b) x))
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

  opaque
    skip-≤ⁱ : ∀ {s c}
            → Reflects (Σ[ s' ꞉ A ] (c ＝ AnSkip s') × is-true (leq s s')) (AnSkip s ≤ⁱ c)
    skip-≤ⁱ {s} {c} =
      ≃→reflects
        (Σ-assoc ⁻¹ ∙ Σ-ap-snd λ s' → Σ-ap-snd λ e → =→≃ (ap (is-true ∘ all2?₁ leq [ s ]₁ ∘ annos) e))
        (reflects-and2 (reflects-strip-skip c) reflects-id)

    assign-≤ⁱ : ∀ {x e s c}
              → Reflects (Σ[ s' ꞉ A ] (c ＝ AnAssign x e s') × is-true (leq s s')) (AnAssign x e s ≤ⁱ c)
    assign-≤ⁱ {s} {c} =
      ≃→reflects
        (Σ-assoc ⁻¹ ∙ Σ-ap-snd λ s' → Σ-ap-snd λ e → =→≃ (ap (is-true ∘ all2?₁ leq [ s ]₁ ∘ annos) e))
        (reflects-and2 (reflects-strip-assign c) reflects-id)

    seq-≤ⁱ : ∀ {c₁ c₂ c}
           → Reflects (Σ[ c₃ ꞉ AnInstr A ] Σ[ c₄ ꞉ AnInstr A ]
                             (c ＝ AnSeq c₃ c₄)
                           × is-true (c₁ ≤ⁱ c₃) × is-true (c₂ ≤ⁱ c₄))
                      (AnSeq c₁ c₂ ≤ⁱ c)
    seq-≤ⁱ {c₁} {c₂} {c} =
      ≃→reflects
          (  Σ-assoc ⁻¹ ∙ Σ-ap-snd λ c₃ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ c₄ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ e → Σ-assoc ⁻¹
           ∙ (Σ-ap-snd λ e₂ →
                 (Σ-ap-snd λ _ →
                     =→≃ (  ap (is-true ∘ all2?₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) e
                          ∙ ap is-true (all2?-++₁ {as = annos c₁}
                                          (length-annos-same {c₁ = c₁}
                                                             (reflects-true (reflects-instr (strip c₁) (strip c₃)) (e₂ ⁻¹)))))
                   ∙ and-true-≃ {x = all2?₁ leq (annos c₁) (annos c₃)} {y = all2?₁ leq (annos c₂) (annos c₄)})
               ∙ ×-ap (reflects-injₑ (instr-is-set (strip c₄) (strip c₂)) (hlevel 1 ⦃ x = H-Level-is-true ⦄)
                        (reflects-instr (strip c₄) (strip c₂))
                        (subst (Reflects⁰ (is-true (strip c₂ ==ⁱ strip c₄))) (sym-instr {c₁ = strip c₂}) reflects-id)) refl
               ∙ ×-assoc ∙ ×-ap ×-swap refl ∙ ×-assoc ⁻¹)
           ∙ ×-ap (reflects-injₑ (instr-is-set (strip c₃) (strip c₁)) (hlevel 1 ⦃ x = H-Level-is-true ⦄)
                     (reflects-instr (strip c₃) (strip c₁))
                     (subst (Reflects⁰ (is-true (strip c₁ ==ⁱ strip c₃))) (sym-instr {c₁ = strip c₁}) reflects-id)) refl
           ∙ ×-assoc
           ∙ ×-ap (and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = all2?₁ leq (annos c₁) (annos c₃)} ⁻¹)
                  (and-true-≃ {x = strip c₂ ==ⁱ strip c₄} {y = all2?₁ leq (annos c₂) (annos c₄)} ⁻¹))
        (reflects-and2 (reflects-strip-seq c) reflects-id)

    ite-≤ⁱ : ∀ {b p₁ c₁ p₂ c₂ q₁ c}
           → Reflects (Σ[ p₃ ꞉ A ] Σ[ c₃ ꞉ AnInstr A ] Σ[ p₄ ꞉ A ] Σ[ c₄ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                            (c ＝ AnITE b p₃ c₃ p₄ c₄ q₂)
                          × is-true (leq p₁ p₃) × is-true (c₁ ≤ⁱ c₃)
                          × is-true (leq p₂ p₄) × is-true (c₂ ≤ⁱ c₄)
                          × is-true (leq q₁ q₂))
                      (AnITE b p₁ c₁ p₂ c₂ q₁ ≤ⁱ c)
    ite-≤ⁱ {p₁} {c₁} {p₂} {c₂} {q₁} {c} =
      ≃→reflects
        (Σ-assoc ⁻¹ ∙ Σ-ap-snd λ p₃ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ c₃ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ p₄ →
         Σ-assoc ⁻¹ ∙ Σ-ap-snd λ c₄ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ q₂ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ e →
             Σ-assoc ⁻¹
           ∙ (Σ-ap-snd λ e₂ →
                  (Σ-ap-snd λ e₃ →
                       =→≃ (  ap (is-true ∘ all2?₁ leq (((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q₁) ∘ annos) e
                            ∙ ap is-true (all2?-∶+₁ {p = leq}
                                                   (  length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
                                                    ∙ ap² (λ x y → suc x + suc y)
                                                          (length-annos-same {c₁ = c₁} (reflects-true (reflects-instr (strip c₁) (strip c₃)) (e₂ ⁻¹)))
                                                          (length-annos-same {c₁ = c₂} (reflects-true (reflects-instr (strip c₂) (strip c₄)) (e₃ ⁻¹)))
                                                    ∙ length₁-++ {xs = p₃ ∷₁ annos c₃} {ys = p₄ ∷₁ annos c₄} ⁻¹)))
                     ∙ and-true-≃ {x = all2?₁ leq ((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ((p₃ ∷₁ annos c₃) ++₁ (p₄ ∷₁ annos c₄))}
                                  {y = leq q₁ q₂}
                     ∙ ×-ap (  =→≃ (ap is-true (all2?-++₁ {p = leq}
                                                          (ap suc (length-annos-same {c₁ = c₁} (reflects-true (reflects-instr (strip c₁) (strip c₃)) (e₂ ⁻¹))))))
                             ∙ and-true-≃ {x = all2?₁ leq (p₁ ∷₁ annos c₁) (p₃ ∷₁ annos c₃)} {y = all2?₁ leq (p₂ ∷₁ annos c₂) (p₄ ∷₁ annos c₄)}) refl
                     ∙ ×-assoc ⁻¹
                     ∙ ×-ap (  =→≃ (ap is-true (all2?-∶∶₁ {p = leq} {xs = annos c₁} {ys = annos c₃}))
                             ∙ and-true-≃ {x = leq p₁ p₃} {y = all2?₁ leq (annos c₁) (annos c₃)})
                            (×-ap (  =→≃ (ap is-true (all2?-∶∶₁ {p = leq} {xs = annos c₂} {ys = annos c₄}))
                                   ∙ and-true-≃ {x = leq p₂ p₄} {y = all2?₁ leq (annos c₂) (annos c₄)}) refl)
                     ∙ ×-assoc ∙ ×-ap (×-assoc ∙ ×-swap ∙ ×-ap refl (×-ap ×-swap refl)) refl ∙ ×-assoc ⁻¹)
                ∙ ×-ap (reflects-injₑ (instr-is-set (strip c₄) (strip c₂)) (hlevel 1 ⦃ x = H-Level-is-true ⦄)
                         (reflects-instr (strip c₄) (strip c₂))
                         (subst (Reflects⁰ (is-true (strip c₂ ==ⁱ strip c₄))) (sym-instr {c₁ = strip c₂}) reflects-id)) refl
                ∙ ×-assoc
                ∙ ×-ap (and-true-≃ {x = strip c₂ ==ⁱ strip c₄} {y = all2?₁ leq (annos c₂) (annos c₄)} ⁻¹) refl
                ∙ ×-assoc ∙ ×-ap ×-swap refl ∙ ×-assoc ⁻¹ ∙ ×-assoc ⁻¹ ∙ ×-assoc ⁻¹)
           ∙ ×-ap (reflects-injₑ (instr-is-set (strip c₃) (strip c₁)) (hlevel 1 ⦃ x = H-Level-is-true ⦄)
                     (reflects-instr (strip c₃) (strip c₁))
                     (subst (Reflects⁰ (is-true (strip c₁ ==ⁱ strip c₃))) (sym-instr {c₁ = strip c₁}) reflects-id)) refl
           ∙ ×-assoc
           ∙ ×-ap (and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = all2?₁ leq (annos c₁) (annos c₃)} ⁻¹) refl
           ∙ ×-assoc ∙ ×-ap ×-swap refl ∙ ×-assoc ⁻¹)
        (reflects-and2 (reflects-strip-ite c) reflects-id)

    while-≤ⁱ : ∀ {inv₁ b p₁ c₁ q₁ c}
             → Reflects (Σ[ inv₂ ꞉ A ] Σ[ p₂ ꞉ A ] Σ[ c₂ ꞉ AnInstr A ] Σ[ q₂ ꞉ A ]
                              (c ＝ AnWhile inv₂ b p₂ c₂ q₂)
                            × is-true (leq inv₁ inv₂) × is-true (leq p₁ p₂)
                            × is-true (c₁ ≤ⁱ c₂) × is-true (leq q₁ q₂))
                        (AnWhile inv₁ b p₁ c₁ q₁ ≤ⁱ c)
    while-≤ⁱ {inv₁} {b} {p₁} {c₁} {q₁} {c} =
      ≃→reflects
        (Σ-assoc ⁻¹ ∙ Σ-ap-snd λ inv₂ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ p₂ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ c₂ →
         Σ-assoc ⁻¹ ∙ Σ-ap-snd λ q₂ → Σ-assoc ⁻¹ ∙ Σ-ap-snd λ e →
           (Σ-ap-snd λ e₂ →
                =→≃ (  ap (is-true ∘ all2?₁ leq ((inv₁ ∷₁ (p₁ ∷₁ annos c₁)) ∶+₁ q₁) ∘ annos) e
                     ∙ ap is-true (all2?-∶+₁ {p = leq} {xs = inv₁ ∷₁ (p₁ ∷₁ annos c₁)} {ys = inv₂ ∷₁ (p₂ ∷₁ annos c₂)}
                                             (ap (2 +_) (length-annos-same {c₁ = c₁} (reflects-true (reflects-instr (strip c₁) (strip c₂)) (e₂ ⁻¹))))))
              ∙ and-true-≃ {x = all2?₁ leq (inv₁ ∷₁ (p₁ ∷₁ annos c₁)) (inv₂ ∷₁ (p₂ ∷₁ annos c₂))}
                                  {y = leq q₁ q₂}
              ∙ ×-ap (  =→≃ (ap is-true (all2?-∶∶₁ {p = leq} {x = inv₁} {y = inv₂} {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}))
                      ∙ and-true-≃ {x = leq inv₁ inv₂} {y = all2?₁ leq (p₁ ∷₁ annos c₁) (p₂ ∷₁ annos c₂)}
                      ∙ ×-ap refl (  =→≃ (ap is-true (all2?-∶∶₁ {p = leq} {x = p₁} {y = p₂} {xs = annos c₁} {ys = annos c₂}))
                                   ∙ and-true-≃ {x = leq p₁ p₂} {y = all2?₁ leq (annos c₁) (annos c₂)}
                                   ∙ ×-swap)
                      ∙ ×-assoc ∙ ×-ap ×-swap refl ∙ ×-assoc ⁻¹) refl
              ∙ ×-assoc ⁻¹)
         ∙ ×-ap (reflects-injₑ (instr-is-set (strip c₂) (strip c₁)) (hlevel 1 ⦃ x = H-Level-is-true ⦄)
                   (reflects-instr (strip c₂) (strip c₁))
                   (subst (Reflects⁰ (is-true (strip c₁ ==ⁱ strip c₂))) (sym-instr {c₁ = strip c₁}) reflects-id)) refl
         ∙ ×-assoc
         ∙ ×-ap (and-true-≃ {x = strip c₁ ==ⁱ strip c₂} {y = all2?₁ leq (annos c₁) (annos c₂)} ⁻¹) refl
         ∙ ×-assoc ∙ ×-ap ×-swap refl ∙ ×-assoc ⁻¹ ∙ ×-assoc ⁻¹)
        (reflects-and2 (reflects-strip-while c) reflects-id)

  mono-post : ∀ {c₁ c₂} → is-true (c₁ ≤ⁱ c₂) → is-true (leq (post c₁) (post c₂))
  mono-post {c₁} {c₂} c =
    (and-true-≃ {x = all id (zip-with leq (annos c₁ .init) (annos c₂ .init))}
                {y = leq (annos c₁ .last) (annos c₂ .last)} $
       (and-true-≃ {x = strip c₁ ==ⁱ strip c₂} {y = all2?₁ leq (annos c₁) (annos c₂)} $ c) .snd) .snd

  mono2-stepA : ∀ {f : String → AExpr → A → A} {g : BExpr → A → A} {c₁ c₂}
              → (∀ {x e s₁ s₂} → is-true (leq s₁ s₂) → is-true (leq (f x e s₁) (f x e s₂)))
              → (∀ {b s₁ s₂} → is-true (leq s₁ s₂) → is-true (leq (g b s₁) (g b s₂)))
              → is-true (c₁ ≤ⁱ c₂)
              → ∀ {s₁ s₂} → is-true (leq s₁ s₂) → is-true (stepA f g s₁ c₁ ≤ⁱ stepA f g s₂ c₂)
  mono2-stepA {f} {g} {c₁ = AnSkip p}              {c₂} fm gm lc {s₁} {s₂} ls =
    let (s' , eq , _) = true-reflects (skip-≤ⁱ {c = c₂}) lc in
    reflects-true (skip-≤ⁱ {c = stepA f g s₂ c₂})
                  (s₂ , ap (stepA f g s₂) eq , ls)
  mono2-stepA {f} {g} {c₁ = AnAssign x e p}        {c₂} fm gm lc {s₁} {s₂} ls =
    let (s' , eq , _) = true-reflects (assign-≤ⁱ {c = c₂}) lc in
    reflects-true (assign-≤ⁱ {c = stepA f g s₂ c₂})
                  (f x e s₂ , ap (stepA f g s₂) eq , fm ls)
  mono2-stepA {f} {g} {c₁ = AnSeq c₃ c₄}           {c₂} fm gm lc {s₁} {s₂} ls =
    let (a₁ , a₂ , eq , le₁ , le₂) = true-reflects (seq-≤ⁱ {c = c₂}) lc in
    reflects-true (seq-≤ⁱ {c = stepA f g s₂ c₂})
                  ( stepA f g s₂ a₁
                  , stepA f g (post a₁) a₂
                  , ap (stepA f g s₂) eq
                  , mono2-stepA {c₁ = c₃} fm gm le₁ ls
                  , mono2-stepA {c₁ = c₄} fm gm le₂ (mono-post {c₁ = c₃} le₁))
  mono2-stepA {f} {g} {c₁ = AnITE b p₀ c₀ p₁ c₁ q} {c₂} fm gm lc {s₁} {s₂} ls =
    let (p₃ , c₃ , p₄ , c₄ , q₂ , eq , le₁ , le₂ , le₃ , le₄ , _) = true-reflects (ite-≤ⁱ {c = c₂}) lc in
    reflects-true (ite-≤ⁱ {c = stepA f g s₂ c₂})
                  ( g b s₂ , stepA f g p₃ c₃ , g (BNot b) s₂ , stepA f g p₄ c₄ , sup (post c₃) (post c₄)
                  , ap (stepA f g s₂) eq
                  , gm ls
                  , mono2-stepA {c₁ = c₀} fm gm le₂ le₁
                  , gm ls
                  , mono2-stepA {c₁ = c₁} fm gm le₄ le₃
                  , leq-sup-l (leq-sup-r1 (mono-post {c₁ = c₀} le₂))
                              (leq-sup-r2 (mono-post {c₁ = c₁} le₄)))
  mono2-stepA {f} {g} {c₁ = AnWhile inv₁ b p c₁ q} {c₂} fm gm lc {s₁} {s₂} ls =
    let (inv₂ , p₂ , c₀ , q₂ , eq , le₁ , le₂ , le₃ , _) = true-reflects (while-≤ⁱ {c = c₂}) lc in
    reflects-true (while-≤ⁱ {c = stepA f g s₂ c₂})
                  ( sup s₂ (post c₀) , g b inv₂ , stepA f g p₂ c₀ , g (BNot b) inv₂
                  , ap (stepA f g s₂) eq
                  , leq-sup-l (leq-sup-r1 ls) (leq-sup-r2 (mono-post {c₁ = c₁} le₃))
                  , gm le₁
                  , mono2-stepA {c₁ = c₁} fm gm le₃ le₂
                  , gm le₁)

  step : A → AnInstr A → AnInstr A
  step = stepA {!!} {!!}
