module Nipkow.Collecting where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming (elim to elimᵇ)
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.List.Correspondences.Binary.All2
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects renaming (dmap to dmapʳ)

open import List1
open import Nipkow.Lang
open import Nipkow.ACom

-- version with a propositional leq

module CollsemA
  (A : 𝒰 (ℓsuc 0ℓ))
  (sup : A → A → A)
  (leq : A → A → 𝒰 (ℓsuc 0ℓ))
  (leq-sup-r1 : ∀ {x a b} → leq x a → leq x (sup a b))
  (leq-sup-r2 : ∀ {x a b} → leq x b → leq x (sup a b))
  (leq-sup-l : ∀ {x a b} → leq a x → leq b x → leq (sup a b) x)
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
      let (s' , eq) = true-reflects (reflects-strip-skip c)
                        (reflects-true (reflects-instr (strip (AnSkip s)) (strip c)) h1) in
      s' , eq , subst (leq s) (ap post eq) h3

    assign-≤ⁱ-l : ∀ {x e s c}
                → (s' : A) → c ＝ AnAssign x e s' → leq s s'
                → AnAssign x e s ≤ⁱ c
    assign-≤ⁱ-l {x} {e} {s} s' eq le =
      subst (AnAssign x e s ≤ⁱ_) (eq ⁻¹) (refl , ([] , le))

    assign-≤ⁱ-r : ∀ {x e s c}
                → AnAssign x e s ≤ⁱ c
                → Σ[ s' ꞉ A ] (c ＝ AnAssign x e s') × leq s s'
    assign-≤ⁱ-r {x} {e} {s} {c} (h1 , h2 , h3) =
      let (s' , eq) = true-reflects (reflects-strip-assign c)
                        (reflects-true (reflects-instr (strip (AnAssign x e s)) (strip c)) h1) in
      s' , eq , subst (leq s) (ap post eq) h3

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
      let (a₁ , a₂ , eq₁ , eq₂ , eq₃) = true-reflects (reflects-strip-seq c)
                                          (reflects-true (reflects-instr (Seq (strip c₁) (strip c₂)) (strip c)) h1)
          (le1 , le2) = All2₁-split
                          (length-annos-same {c₁ = c₁}
                             (reflects-true (reflects-instr (strip c₁) (strip a₁)) (eq₂ ⁻¹)))
                          (subst (All2₁ leq (annos c₁ ++₁ annos c₂) ∘ annos) eq₁ h2)
         in
        a₁ , a₂ , eq₁ , (eq₂ ⁻¹ , le1) , eq₃ ⁻¹ , le2

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
      let (p₃ , a₁ , p₄ , a₂ , q , eq , eq₁ , eq₂) = true-reflects (reflects-strip-ite c)
                                                             (reflects-true (reflects-instr (ITE b (strip c₁) (strip c₂)) (strip c)) h1)
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
      let (inv₂ , p , a , q , eq , eq₁) = true-reflects (reflects-strip-while c)
                                            (reflects-true (reflects-instr (While b (strip c₁)) (strip c)) h1)
          le = All2₁-∶+₁-l (ap (2 +_)
                              (length-annos-same {c₁ = c₁}
                                                 (reflects-true (reflects-instr (strip c₁) (strip a)) (eq₁ ⁻¹)))) $
               subst (All2₁ leq (((inv₁ ∷₁ (p₁ ∷₁ annos c₁)) ∶+₁ q₁)) ∘ annos) eq h2
          le1 = All2-∶∶₁-l (le .fst)
          le2 = All2-∶∶₁-l (le1 .snd)
       in
      inv₂ , p , a , q , eq , le1 .fst , le2 .fst , (eq₁ ⁻¹ , le2 .snd) , le .snd

  mono-post : ∀ {c₁ c₂} → c₁ ≤ⁱ c₂ → leq (post c₁) (post c₂)
  mono-post (_ , _ , h) = h

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
