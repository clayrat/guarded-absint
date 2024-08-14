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

open import Combinatorics.Power
open import Order.Base
open import Order.Diagram.Lub
open import Order.SupLattice
open import Order.SupLattice.SmallBasis
open import Order.SupLattice.SmallPresentation

open import List1
open import Nipkow.Lang
open import Nipkow.ACom
open import Nipkow.ACom.Leq

module AnInstrOrd {B : 𝒰}
  (P : Poset (ℓsuc 0ℓ) 0ℓ)
  (L : is-sup-lattice P 0ℓ)
  (β : B → ⌞ P ⌟)
  (h : is-basis P L β)
  (sp : has-small-presentation P L β h)
  where

  open Poset P
  open is-lub
  open is-sup-lattice L
  open is-basis h
  open AnInstrLeq Ob _≤_ ≤-thin ≤-refl ≤-trans ≤-antisym

  an-poset : Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  an-poset .Poset.Ob        = AnInstr Ob
  an-poset .Poset._≤_       = _≤ⁱ_
  an-poset .Poset.≤-thin    = hlevel 1
  an-poset .Poset.≤-refl    = ≤ⁱ-refl
  an-poset .Poset.≤-trans   = ≤ⁱ-trans
  an-poset .Poset.≤-antisym = ≤ⁱ-antisym

  -- however we need more structure to form a suplattice
  anc-poset : Instr → Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  anc-poset c .Poset.Ob                    = AnStr Ob c
  anc-poset c .Poset._≤_ (a1 , _) (a2 , _) = a1 ≤ⁱ a2
  anc-poset c .Poset.≤-thin                = hlevel 1
  anc-poset c .Poset.≤-refl                = ≤ⁱ-refl
  anc-poset c .Poset.≤-trans               = ≤ⁱ-trans
  anc-poset c .Poset.≤-antisym xy yx       =
    Σ-prop-path (λ a → instr-is-set (strip a) c) (≤ⁱ-antisym xy yx)

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

  -- small basis via annotation

  annotate-bot : ∀ {c a}
               → strip a ＝ c
               → annotate (λ _ → bot) c ≤ⁱ a
  annotate-bot {c} {a} e =
    =all→≤ⁱ (strip-annotate ∙ e ⁻¹)
      (subst (λ q → All²₁ _≤_ q (annos a))
            (annos-annotate-const ⁻¹)
            (subst (λ q → All²₁ _≤_ (replicate₁ q bot) (annos a))
                   (length₁-annos {a = a} ∙ ap asize e)
                   (All²₁-replicate-l has-bot)))

  unᵐ-β : Maybe B → Ob
  unᵐ-β = recᵐ bot β

  single-at : ∀ {ℓᵇ} {B : 𝒰 ℓᵇ}
            → B → ℕ → ℕ → Maybe B
  single-at b n k = if n ==ⁿ k then just b else nothing

  shr : (ℕ → Maybe B) → ℕ → ℕ → Maybe B
  shr f n k = if n ≤? k then f (k ∸ n) else nothing

  filt : (ℕ → Maybe B) → (ℕ → Bool) → ℕ → Maybe B
  filt f p n = if p n then f n else nothing

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

  annotate-β : (c : Instr) → (ℕ → Maybe B) → AnInstr Ob
  annotate-β c f = annotate (unᵐ-β ∘ f) c

  annotate-β-filt : ∀ {c : Instr} {f : ℕ → Maybe B} {p : ℕ → Bool}
                  → (∀ n → n <ⁿ asize c → is-true (p n))
                  → annotate-β c (filt f p) ＝ annotate-β c f
  annotate-β-filt h = annotate-ext λ n lt → ap unᵐ-β (if-true (h n lt))

  anc-β : (c : Instr) → (ℕ → Maybe B) → AnStr Ob c
  anc-β c f = annotate-β c f , strip-annotate

  anc-is-small : (c : Instr) (x : AnStr Ob c) (b : ℕ → Maybe B) → is-of-size 0ℓ (annotate-β c b ≤ⁱ x .fst)
  anc-is-small c x b = ≃→is-of-size (≤ⁱ≃=all ⁻¹) (size 0ℓ ⦃ s = Size-Σ ⦃ sa = Size-default ⦄ ⦄)

  anc-↓-is-sup : (c : Instr) (x : AnStr Ob c) → is-lub (anc-poset c) (↓ᴮ-inclusion (anc-poset c) (anc-suplat c) (anc-β c) x) x
  anc-↓-is-sup Skip (a , e) =
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
    }
  anc-↓-is-sup (Assign x e) (a , eq) =
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
    }
  anc-↓-is-sup (Seq c₁ c₂) (a , eq) =
    let ih₁ = anc-↓-is-sup c₁
        ih₂ = anc-↓-is-sup c₂
        (a₁ , a₂ , eq₀ , e₁ , e₂) = strip-seq-r eq
      in
    record {
      fam≤lub = λ where (bf , le) →
                           let (a1 , a2 , eq0 , le1 , le2) = seq-≤ⁱ-eliml le
                               (e1 , e2) = AnSeq-inj (eq0 ⁻¹ ∙ eq₀)
                             in
                           seq-≤ⁱ-introl eq0
                              (ih₁ (a1 , ap strip e1 ∙ e₁) .fam≤lub (bf , le1))
                              (ih₂ (a2 , ap strip e2 ∙ e₂) .fam≤lub (shl bf (asize c₁) , le2))
    ; least = λ where (a'' , eq'') f →
                        let (a₁' , a₂' , eq₀' , e₁' , e₂') = strip-seq-r eq'' in
                        subst (_≤ⁱ a'') (eq₀ ⁻¹) $
                        seq-≤ⁱ-introl eq₀'
                          (ih₁ (a₁ , e₁) .least (a₁' , e₁')
                             λ where (bf , le) →
                                         let bf₁ = filt bf (_<? asize c₁) in
                                         subst (_≤ⁱ a₁') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt))
                                           ((seq-≤ⁱ-elim $
                                             subst (annotate-β (Seq c₁ c₂) bf₁ ≤ⁱ_) eq₀' $
                                             f ( bf₁
                                               , seq-≤ⁱ-introl eq₀
                                                   (subst (_≤ⁱ a₁) (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt) ⁻¹) le)
                                                   (subst (λ q → annotate q c₂ ≤ⁱ a₂)
                                                          (shl-filt-not {f = bf} {p = _<? asize c₁} {n = asize c₁}
                                                             (λ m le → reflects-false (<-reflects m (asize c₁)) (≤≃≯ $ le)) ⁻¹)
                                                          (annotate-bot e₂))))
                                             .fst))
                          (ih₂ (a₂ , e₂) .least (a₂' , e₂')
                             λ where (bf , le) →
                                        let bf₂ = shr bf (asize c₁) in
                                        subst (λ q → annotate q c₂ ≤ⁱ a₂') (shl-shr {f = bf} {n = asize c₁})
                                          ((seq-≤ⁱ-elim $
                                            subst (annotate-β (Seq c₁ c₂) bf₂ ≤ⁱ_) eq₀' $
                                            f ( bf₂
                                              , seq-≤ⁱ-introl eq₀
                                                  (subst (_≤ⁱ a₁)
                                                         (annotate-ext {c = c₁} {f = λ _ → bot} {g = unᵐ-β ∘ shr bf (asize c₁)}
                                                              λ n lt → ap unᵐ-β (if-false {b = asize c₁ ≤? n} (reflects-false (≤-reflects (asize c₁) n) (<≃≱ $ lt))) ⁻¹)
                                                         (annotate-bot e₁))
                                                  (subst (λ q → annotate q c₂ ≤ⁱ a₂) (shl-shr {f = bf} {n = asize c₁} ⁻¹) le)))
                                            .snd))

    }
  anc-↓-is-sup (ITE b c₁ c₂) (a , eq) =
    let ih₁ = anc-↓-is-sup c₁
        ih₂ = anc-↓-is-sup c₂
        (p₁ , a₁ , p₂ , a₂ , q , eq₀ , e₁ , e₂) = strip-ite-r eq
     in
    record {
      fam≤lub = λ where (bf , le) →
                          let (p1 , a1 , p2 , a2 , q0 , eq0 , le1 , le2 , le3 , le4 , le5) = ite-≤ⁱ-eliml le
                              (_ , _ , e2 , _ , e4 , _) = AnITE-inj (eq0 ⁻¹ ∙ eq₀)
                            in
                          ite-≤ⁱ-introl eq0 le1
                            (ih₁ (a1 , ap strip e2 ∙ e₁) .fam≤lub (shl bf 1 , le2))
                            le3
                            (ih₂ (a2 , ap strip e4 ∙ e₂) .fam≤lub (shl bf (2 + asize c₁) , le4))
                            le5
    ; least = λ where (a'' , eq'') f →
                        let (p₁' , a₁' , p₂' , a₂' , q' , eq₀' , e₁' , e₂') = strip-ite-r eq'' in
                        subst (_≤ⁱ a'') (eq₀ ⁻¹) $
                        ite-≤ⁱ-introl eq₀'
                          (↓-is-sup p₁ .least p₁'
                             λ where (b' , le) →
                                        let bf₁ = single-at b' 0 in
                                        (ite-≤ⁱ-elim $
                                         subst (annotate-β (ITE b c₁ c₂) bf₁ ≤ⁱ_) eq₀' $
                                         f ( bf₁
                                           , ite-≤ⁱ-introl eq₀ le
                                                (subst (λ q → annotate q c₁ ≤ⁱ a₁) (shl-single-at-not z<s ⁻¹)
                                                       (annotate-bot e₁))
                                                (has-bot p₂)
                                                (subst (λ q → annotate q c₂ ≤ⁱ a₂) (shl-single-at-not z<s ⁻¹)
                                                       (annotate-bot e₂))
                                                (has-bot q)))
                                         .fst)
                          (ih₁ (a₁ , e₁) .least (a₁' , e₁')
                              λ where (bf , le) →
                                        let bf₂ = shr (filt bf (_<? asize c₁)) 1 in
                                        subst (_≤ⁱ a₁') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₁)) lt)) $
                                        subst (λ q → annotate q c₁ ≤ⁱ a₁') (shl-shr {f = filt bf (_<? asize c₁)} {n = 1}) $
                                        ite-≤ⁱ-elim
                                           (subst (annotate-β (ITE b c₁ c₂) bf₂ ≤ⁱ_) eq₀' $
                                            f ( bf₂
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
                                        let bf₃ = single-at b' (1 + asize c₁) in
                                        subst (_≤ p₂') (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c₁) (asize c₁)) refl))) $
                                        ite-≤ⁱ-elim
                                          (subst (annotate-β (ITE b c₁ c₂) bf₃ ≤ⁱ_) eq₀' $
                                           f ( bf₃
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
                          (ih₂ (a₂ , e₂) .least (a₂' , e₂')
                              λ where (bf , le) →
                                        let bf₄ = shr (filt bf (_<? asize c₂)) (2 + asize c₁) in
                                        subst (_≤ⁱ a₂') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c₂)) lt)) $
                                        subst (λ q → annotate q c₂ ≤ⁱ a₂')
                                              (shl-shr {f = filt bf (_<? asize c₂)} {n = 2 + asize c₁}) $
                                        ite-≤ⁱ-elim
                                          (subst (annotate-β (ITE b c₁ c₂) bf₄ ≤ⁱ_) eq₀' $
                                           f ( bf₄
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
                                        let bf₅ = single-at b' (2 + asize c₁ + asize c₂) in
                                        subst (_≤ q')
                                              (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c₁ + asize c₂) (asize c₁ + asize c₂)) refl))) $
                                        ite-≤ⁱ-elim
                                          (subst (annotate-β (ITE b c₁ c₂) bf₅ ≤ⁱ_) eq₀' $
                                           f ( bf₅
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
  anc-↓-is-sup (While b c) (a , eq) =
    let ih = anc-↓-is-sup c
        (inv₀ , p₀ , a₀ , q₀ , eq₀ , e₀) = strip-while-r eq
      in
    record {
      fam≤lub = λ where (bf , le) →
                           let (inv0 , p0 , c0 , q0 , eq0 , le1 , le2 , le3 , le4) = while-≤ⁱ-eliml le
                               (e1 , _ , e2 , e3 , e4) = AnWhile-inj (eq0 ⁻¹ ∙ eq₀)
                             in
                           while-≤ⁱ-introl eq0 le1 le2
                             (ih (c0 , ap strip e3 ∙ e₀) .fam≤lub (shl bf 2 , le3))
                             le4
    ; least = λ where (a'' , eq'') f →
                        let (inv₀' , p₀' , a₀' , q₀' , eq₀' , e₀') = strip-while-r eq'' in
                        subst (_≤ⁱ a'') (eq₀ ⁻¹) $
                        while-≤ⁱ-introl eq₀'
                          (↓-is-sup inv₀ .least inv₀'
                             λ where (b' , le) →
                                        let bf₁ = single-at b' 0 in
                                        (while-≤ⁱ-elim $
                                         subst (annotate-β (While b c) bf₁ ≤ⁱ_) eq₀' $
                                         f ( bf₁
                                           , while-≤ⁱ-introl eq₀ le
                                                (has-bot p₀)
                                                (subst (λ q → annotate q c ≤ⁱ a₀)
                                                       (shl-single-at-not {n = 0} {m = 2} z<s ⁻¹)
                                                       (annotate-bot e₀))
                                                (has-bot q₀)))
                                         .fst)
                          (↓-is-sup p₀ .least p₀'
                             λ where (b' , le) →
                                       let bf₂ = single-at b' 1 in
                                       (while-≤ⁱ-elim $
                                        subst (annotate-β (While b c) bf₂ ≤ⁱ_) eq₀' $
                                        f ( bf₂
                                          , while-≤ⁱ-introl eq₀
                                              (has-bot inv₀)
                                              le
                                              (subst (λ q → annotate q c ≤ⁱ a₀)
                                                       (shl-single-at-not {n = 1} {m = 2} (s<s z<s) ⁻¹)
                                                       (annotate-bot e₀))
                                              (has-bot q₀)))
                                        .snd .fst)
                          (ih (a₀ , e₀) .least (a₀' , e₀')
                              λ where (bf , le) →
                                       let bf₃ = shr (filt bf (_<? asize c)) 2 in
                                        subst (_≤ⁱ a₀') (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c)) lt)) $
                                        subst (λ q → annotate q c ≤ⁱ a₀')
                                              (shl-shr {f = filt bf (_<? asize c)} {n = 2}) $
                                        while-≤ⁱ-elim
                                          (subst (annotate-β (While b c) bf₃ ≤ⁱ_) eq₀' $
                                           f ( bf₃
                                             , while-≤ⁱ-introl eq₀
                                                 (has-bot inv₀)
                                                 (has-bot p₀)
                                                 (subst (λ q → annotate q c ≤ⁱ a₀)
                                                         (shl-shr {f = filt bf (_<? asize c)} {n = 2} ⁻¹) $
                                                  subst (_≤ⁱ a₀) (annotate-β-filt (λ n lt → reflects-true (<-reflects n (asize c)) lt) ⁻¹) le)
                                                 (subst (λ z → unᵐ-β z ≤ q₀)
                                                        (if-false (reflects-false (<-reflects (asize c) (asize c)) <-irr) ⁻¹)
                                                        (has-bot q₀))
                                             ))
                                          .snd .snd .fst)
                          (↓-is-sup q₀ .least q₀'
                             λ where (b' , le) →
                                       let bf₄ = single-at b' (2 + asize c) in
                                       subst (_≤ q₀') (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c) (asize c)) refl))) $
                                       while-≤ⁱ-elim
                                        (subst (annotate-β (While b c) bf₄ ≤ⁱ_) eq₀' $
                                         f ( bf₄
                                           , while-≤ⁱ-introl eq₀
                                               (has-bot inv₀)
                                               (has-bot p₀)
                                               (subst (_≤ⁱ a₀)
                                                      (annotate-ext λ n lt → ap unᵐ-β (if-false (reflects-false (==ⁿ-reflects (2 + asize c) (n + 2))
                                                                                                   (contra
                                                                                                      (λ e → =→≤ (+-inj-r (asize c) n 2 (+-comm (asize c) 2 ∙ e)))
                                                                                                      (<→≱ $ lt)))) ⁻¹)
                                                      (annotate-bot e₀))
                                               (subst (_≤ q₀)
                                                 (ap unᵐ-β (if-true (reflects-true (==ⁿ-reflects (asize c) (asize c)) refl)) ⁻¹)
                                                 le)))
                                       .snd .snd .snd)
    }

  anc-bas : ∀ c → is-basis (anc-poset c) (anc-suplat c) (anc-β c)
  anc-bas c = record { ≤-is-small = anc-is-small c ; ↓-is-sup = anc-↓-is-sup c }

  -- small presentation

  J : 𝒰
  J = sp .fst .fst
  Y : J → ℙ B 0ℓ
  Y = sp .fst .snd .fst
  R : ℙ (B × ℙ B 0ℓ) 0ℓ
  R = sp .fst .snd .snd
  isp : is-a-small-presentation P L β h (J , Y , R)
  isp = sp .snd
