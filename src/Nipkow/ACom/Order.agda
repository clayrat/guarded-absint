module Nipkow.ACom.Order where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat renaming (_==_ to _==ⁿ_ ; rec to recⁿ)
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
open import Order.Constructions.Product
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
  open AnInstrLeq Ob _≤_
  open AnInstrLeqProp Ob _≤_ ≤-thin ≤-refl ≤-trans ≤-antisym

{-
  an-poset : Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  an-poset .Poset.Ob        = AnInstr Ob
  an-poset .Poset._≤_       = _≤ⁱ_
  an-poset .Poset.≤-thin    = hlevel 1
  an-poset .Poset.≤-refl    = ≤ⁱ-refl
  an-poset .Poset.≤-trans   = ≤ⁱ-trans
  an-poset .Poset.≤-antisym = ≤ⁱ-antisym
-}

  -- we need more structure to form a suplattice
  anc-poset : Instr → Poset (ℓsuc 0ℓ) (ℓsuc 0ℓ)
  anc-poset c .Poset.Ob                    = AnStr Ob c
  anc-poset c .Poset._≤_ (a1 , _) (a2 , _) = a1 ≤ⁱ a2
  anc-poset c .Poset.≤-thin                = hlevel 1
  anc-poset c .Poset.≤-refl                = ≤ⁱ-refl
  anc-poset c .Poset.≤-trans               = ≤ⁱ-trans
  anc-poset c .Poset.≤-antisym xy yx       = Σ-prop-path! (≤ⁱ-antisym xy yx)

  anc-lub : ∀ c {I : 𝒰} (F : I → AnStr Ob c)
          → Lub (anc-poset c) F
  anc-lub  Skip             F =
    let l = lubs (λ j → let (a , _) = strip-skip (F j .snd) in a) in
    ≃→Lub′ (AnStr-Skip-≃ ⁻¹)
      Skip-≤ⁱ skip-≤ⁱ-elim
      l
  anc-lub (Assign x e)      F =
    let l = lubs (λ j → let (a , _) = strip-assign (F j .snd) in a) in
    ≃→Lub′ (AnStr-Assign-≃ ⁻¹)
      (Assign-≤ⁱ refl refl) assign-≤ⁱ-elim
      l
  anc-lub (Seq c₁ c₂)       F =
    let ih₁ = anc-lub c₁ λ i → let (a₁ , _ , _ , e₁ , _) = strip-seq (F i .snd) in a₁ , e₁
        ih₂ = anc-lub c₂ λ i → let (_ , a₂ , _ , _ , e₂) = strip-seq (F i .snd) in a₂ , e₂
      in
    ≃→Lub′ (AnStr-Seq-≃ ⁻¹)
      (λ where (le₁ , le₂) → Seq-≤ⁱ le₁ le₂) seq-≤ⁱ-elim
      (ih₁ × ih₂)
  anc-lub (ITE b c₁ c₂) {I} F =
    let lp₁ = lubs      (λ i → let (p₁ , _  , _  , _  , _ , _ , _  , _ ) = strip-ite (F i .snd) in p₁)
        ih₁ = anc-lub c₁ λ i → let (_  , a₁ , _  , _  , _ , _ , e₁ , _ ) = strip-ite (F i .snd) in a₁ , e₁
        lp₂ = lubs      (λ i → let (_  , _  , p₂ , _  , _ , _ , _  , _ ) = strip-ite (F i .snd) in p₂)
        ih₂ = anc-lub c₂ λ i → let (_  , _  , _  , a₂ , _ , _ , _  , e₂) = strip-ite (F i .snd) in a₂ , e₂
        lq  = lubs      (λ i → let (_  , _  , _  , _  , q , _ , _  , _ ) = strip-ite (F i .snd) in q)
      in
    ≃→Lub′ {P = P ×ₚ (anc-poset c₁ ×ₚ (P ×ₚ (anc-poset c₂ ×ₚ P)))} (AnStr-ITE-≃ ⁻¹)
      (λ where (le₁ , le₂ , le₃ , le₄ , le₅) → ITE-≤ⁱ refl le₁ le₂ le₃ le₄ le₅) ite-≤ⁱ-elim
      (lp₁ × ih₁ × lp₂ × ih₂ × lq)
  anc-lub (While b c)   {I} F =
    let linv = lubs     (λ i → let (inv , _ , _ , _ , _  , _) = strip-while (F i .snd) in inv)
        lp   = lubs     (λ i → let (_   , p , _ , _ , _  , _) = strip-while (F i .snd) in p)
        ih   = anc-lub c λ i → let (_   , _ , a , _ , _  , e) = strip-while (F i .snd) in a , e
        lq   = lubs     (λ i → let (_   , _ , _ , q , _  , _) = strip-while (F i .snd) in q)
      in
    ≃→Lub′ {P = P ×ₚ (P ×ₚ (anc-poset c ×ₚ P))} (AnStr-While-≃ ⁻¹)
      (λ where (le₁ , le₂ , le₃ , le₄) → While-≤ⁱ le₁ refl le₂ le₃ le₄) while-≤ⁱ-elim
      (linv × lp × ih × lq)

  anc-suplat : (c : Instr) → is-sup-lattice (anc-poset c) 0ℓ
  anc-suplat c .is-sup-lattice.has-lubs {F} = anc-lub c F

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
  shl-shr {f} {n} = fun-ext λ k → ap unᵐ-β (  if-true (true→so! ⦃ ≤-reflects ⦄
                                                                (≤-+-l {m = n} {n = k}))
                                            ∙ ap f (+-cancel-∸-r k n))

  shl-filt-not : {f : ℕ → Maybe B} {p : ℕ → Bool} {n : ℕ}
                 → (∀ m → n ≤ⁿ m → ⌞ not (p m) ⌟)
                 → shl (unᵐ-β ∘ filt f p) n ＝ λ _ → bot
  shl-filt-not {n} h = fun-ext λ k → ap unᵐ-β (if-false (h (k + n) ≤-+-l))

  shl-single-at-not : {b : B} {n m : ℕ}
                  → n <ⁿ m
                  → shl (unᵐ-β ∘ single-at b n) m ＝ λ _ → bot
  shl-single-at-not {n} {m} lt =
    fun-ext λ k → ap unᵐ-β (if-false (false→so! ⦃ Reflects-ℕ-Path ⦄
                                                (contra (λ e → subst (m ≤ⁿ_) (e ⁻¹) (≤-+-l))
                                                        (<→≱ $ lt))))

  annotate-β : (c : Instr) → (ℕ → Maybe B) → AnInstr Ob
  annotate-β c f = annotate (unᵐ-β ∘ f) c

  annotate-β-filt : ∀ {c : Instr} {f : ℕ → Maybe B} {p : ℕ → Bool}
                  → (∀ n → n <ⁿ asize c → ⌞ p n ⌟)
                  → annotate-β c (filt f p) ＝ annotate-β c f
  annotate-β-filt h = annotate-ext λ n lt → ap unᵐ-β (if-true (h n lt))

  anc-β : (c : Instr) → (ℕ → Maybe B) → AnStr Ob c
  anc-β c f = annotate-β c f , strip-annotate

  anc-is-small : (c : Instr) (x : AnStr Ob c) (b : ℕ → Maybe B) → is-of-size 0ℓ (annotate-β c b ≤ⁱ x .fst)
  anc-is-small c x b = ≃→is-of-size (≤ⁱ≃=all ⁻¹) (size 0ℓ ⦃ s = Size-Σ ⦃ sa = Size-default ⦄ ⦄)

  anc-↓-is-sup : (c : Instr) (x : AnStr Ob c) → is-lub (anc-poset c)
                                                       (↓ᴮ-inclusion (anc-poset c) (anc-suplat c) (anc-β c) x) x
  anc-↓-is-sup Skip (a , e) =
    let (o' , e') = strip-skip e in
    record {
      fam≤lub = λ where (bf , le) → le
    ; least = λ where (a'' , e'') f →
                        let (oo , eo) = strip-skip e'' in
                        skip-≤ⁱ-intro2 e' eo $
                        ↓-is-sup o' .least oo λ where (b , le) →
                                                        skip-≤ⁱ-elim2 refl eo $
                                                        f (single-at b 0 , skip-≤ⁱ-intro2 refl e' le)
    }
  anc-↓-is-sup (Assign x e) (a , eq) =
    let (o' , eq') = strip-assign eq in
    record {
      fam≤lub = λ where (bf , le) → le
    ; least = λ where (a'' , eq'') f →
                        let (oo , eo) = strip-assign eq'' in
                        assign-≤ⁱ-intro2 eq' eo $
                        ↓-is-sup o' .least oo λ where (b , le) →
                                                         assign-≤ⁱ-elim2 refl eo $
                                                         f (single-at b 0 , assign-≤ⁱ-intro2 refl eq' le)
    }
  anc-↓-is-sup (Seq c₁ c₂) (a , eq) =
    let (a₁ , a₂ , eq₀ , e₁ , e₂) = strip-seq eq
        ih₁ = anc-↓-is-sup c₁ (a₁ , e₁)
        ih₂ = anc-↓-is-sup c₂ (a₂ , e₂)
      in
    record {
      fam≤lub = λ where (bf , le) →
                           let (le1 , le2) = seq-≤ⁱ-elim2 refl eq₀ le in
                           seq-≤ⁱ-intro2 refl eq₀
                             (ih₁ .fam≤lub (bf , le1))
                             (ih₂ .fam≤lub (shl bf (asize c₁) , le2))
    ; least = λ where (a'' , eq'') f →
                        let (a₁' , a₂' , eq₀' , e₁' , e₂') = strip-seq eq'' in
                        seq-≤ⁱ-intro2 eq₀ eq₀'
                          (ih₁ .least (a₁' , e₁')
                             λ where (bf , le) →
                                         let bf₁ = filt bf (_<? asize c₁)
                                             p₁ = annotate-β-filt (λ n lt → true→so! ⦃ <-reflects ⦄ lt)
                                           in
                                         subst (_≤ⁱ a₁') p₁
                                           ((seq-≤ⁱ-elim2 refl eq₀' $
                                             f ( bf₁
                                               , seq-≤ⁱ-intro2 refl eq₀
                                                   (subst (_≤ⁱ a₁) (p₁ ⁻¹) le)
                                                   (subst (λ q → annotate q c₂ ≤ⁱ a₂)
                                                          (shl-filt-not {f = bf} {p = _<? asize c₁} {n = asize c₁}
                                                             (λ m le → false→so! ⦃ <-reflects ⦄
                                                                                 (≤≃≯ $ le)) ⁻¹)
                                                          (annotate-bot e₂))))
                                             .fst))
                          (ih₂ .least (a₂' , e₂')
                             λ where (bf , le) →
                                        let bf₂ = shr bf (asize c₁)
                                            p₂ = shl-shr {f = bf} {n = asize c₁}
                                          in
                                        subst (λ q → annotate q c₂ ≤ⁱ a₂') p₂
                                          ((seq-≤ⁱ-elim2 refl eq₀' $
                                            f ( bf₂
                                              , seq-≤ⁱ-intro2 refl eq₀
                                                  (subst (_≤ⁱ a₁)
                                                         (annotate-ext {c = c₁} {f = λ _ → bot} {g = unᵐ-β ∘ shr bf (asize c₁)}
                                                              λ n lt → ap unᵐ-β (if-false {b = asize c₁ ≤? n}
                                                                                          (false→so! ⦃ ≤-reflects ⦄ (<≃≱ $ lt))) ⁻¹)
                                                         (annotate-bot e₁))
                                                  (subst (λ q → annotate q c₂ ≤ⁱ a₂) (p₂ ⁻¹) le)))
                                            .snd))
    }
  anc-↓-is-sup (ITE b c₁ c₂) (a , eq) =
    let (p₁ , a₁ , p₂ , a₂ , q , eq₀ , e₁ , e₂) = strip-ite eq
        ih₁ = anc-↓-is-sup c₁ (a₁ , e₁)
        ih₂ = anc-↓-is-sup c₂ (a₂ , e₂)
     in
    record {
      fam≤lub = λ where (bf , le) →
                          let (le1 , le2 , le3 , le4 , le5) = ite-≤ⁱ-elim2 refl eq₀ le in
                          ite-≤ⁱ-intro2 refl eq₀ le1
                            (ih₁ .fam≤lub (shl bf 1 , le2))
                            le3
                            (ih₂ .fam≤lub (shl bf (2 + asize c₁) , le4))
                            le5
    ; least = λ where (a'' , eq'') f →
                        let (p₁' , a₁' , p₂' , a₂' , q' , eq₀' , e₁' , e₂') = strip-ite eq'' in
                        ite-≤ⁱ-intro2 eq₀ eq₀'
                          (↓-is-sup p₁ .least p₁'
                             λ where (b' , le) →
                                        let bf₁ = single-at b' 0 in
                                        (ite-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₁
                                           , ite-≤ⁱ-intro2 refl eq₀ le
                                                (subst (λ q → annotate q c₁ ≤ⁱ a₁) (shl-single-at-not z<s ⁻¹)
                                                       (annotate-bot e₁))
                                                (has-bot p₂)
                                                (subst (λ q → annotate q c₂ ≤ⁱ a₂) (shl-single-at-not z<s ⁻¹)
                                                       (annotate-bot e₂))
                                                (has-bot q)))
                                         .fst)
                          (ih₁ .least (a₁' , e₁')
                              λ where (bf , le) →
                                        let bf₂ = shr (filt bf (_<? asize c₁)) 1
                                            p₂₁ = annotate-β-filt (λ n lt → true→so! ⦃ <-reflects ⦄ lt)
                                            p₂₂ = shl-shr {f = filt bf (_<? asize c₁)} {n = 1}
                                          in
                                        subst (_≤ⁱ a₁') p₂₁ $ subst (λ q → annotate q c₁ ≤ⁱ a₁') p₂₂ $
                                        (ite-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₂
                                           , ite-≤ⁱ-intro2 refl eq₀
                                                (has-bot p₁)
                                                (subst (λ q → annotate q c₁ ≤ⁱ a₁) (p₂₂ ⁻¹) $ subst (_≤ⁱ a₁) (p₂₁ ⁻¹) le)
                                                (subst (λ q → unᵐ-β q ≤ p₂) (if-false (false→so! ⦃ <-reflects {m = asize c₁} ⦄ <-irr) ⁻¹ )
                                                    (has-bot p₂))
                                                (subst (_≤ⁱ a₂)
                                                       (annotate-ext λ n lt → ap unᵐ-β (  if-true (true→so! ⦃ <-reflects {n = n + (2 + asize c₁)} ⦄
                                                                                                            (<-+-l z<s))
                                                                                        ∙ if-false (false→so! ⦃ <-reflects ⦄
                                                                                                              (≤→≯ $ ≤ⁿ-trans (≤ⁿ-trans ≤-ascend ≤-+-l)
                                                                                                                              (=→≤ (ap (_∸ 1) (+-suc-r n (1 + asize c₁) ⁻¹)))))) ⁻¹)
                                                       (annotate-bot e₂))
                                                (subst (λ z → unᵐ-β z ≤ q)
                                                       (if-false (false→so! ⦃ <-reflects {m = 1 + asize c₁ + asize c₂} {n = asize c₁} ⦄
                                                                            (≤→≯ $ ≤-suc-r ≤-+-r)) ⁻¹)
                                                       (has-bot q))))
                                         .snd .fst)
                          (↓-is-sup p₂ .least p₂'
                             λ where (b' , le) →
                                        let bf₃ = single-at b' (1 + asize c₁)
                                            p₃ = ap unᵐ-β (if-true (true→so! ⦃ Reflects-ℕ-Path {m = asize c₁} ⦄ refl))
                                          in
                                        subst (_≤ p₂') p₃ $
                                        (ite-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₃
                                           , ite-≤ⁱ-intro2 refl eq₀ (has-bot p₁)
                                               (subst (_≤ⁱ a₁)
                                                      (annotate-ext λ n lt → ap unᵐ-β (if-false (false→so! ⦃ Reflects-ℕ-Path ⦄
                                                                                                           (contra (λ e → =→≤ (suc-inj (e ∙ +-comm n 1))) (<→≱ $ lt)))) ⁻¹)
                                                      (annotate-bot e₁))
                                               (subst (_≤ p₂) (p₃ ⁻¹) le)
                                               (subst (λ q → annotate q c₂ ≤ⁱ a₂)
                                                      (shl-single-at-not {n = 1 + asize c₁} {m = 2 + asize c₁} (s<s <-ascend) ⁻¹)
                                                      (annotate-bot e₂))
                                               (subst (λ z → unᵐ-β z ≤ q)
                                                      (if-false {b = asize c₁ ==ⁿ 1 + asize c₁ + asize c₂}
                                                                (false→so! ⦃ Reflects-ℕ-Path {m = asize c₁} {n = 1 + asize c₁ + asize c₂} ⦄
                                                                           λ p → false! ⦃ Reflects-id≠+-suc ⦄ (p ∙ +-suc-r (asize c₁) (asize c₂) ⁻¹)) ⁻¹)
                                                      (has-bot q))))
                                          .snd .snd .fst)
                          (ih₂ .least (a₂' , e₂')
                              λ where (bf , le) →
                                        let bf₄ = shr (filt bf (_<? asize c₂)) (2 + asize c₁)
                                            p₄₁ = annotate-β-filt (λ n lt → true→so! ⦃ <-reflects ⦄ lt)
                                            p₄₂ = shl-shr {f = filt bf (_<? asize c₂)} {n = 2 + asize c₁}
                                          in
                                        subst (_≤ⁱ a₂') p₄₁ $ subst (λ q → annotate q c₂ ≤ⁱ a₂') p₄₂ $
                                        (ite-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₄
                                           , ite-≤ⁱ-intro2 refl eq₀ (has-bot p₁)
                                                (subst (_≤ⁱ a₁)
                                                       (annotate-ext λ n lt → ap unᵐ-β (if-false {b = 1 + asize c₁ <? n + 1}
                                                                                                 (false→so! ⦃ <-reflects ⦄
                                                                                                            (≤→≯ $ ≤ⁿ-trans (=→≤ (+-comm n 1)) (s≤s (<→≤ lt))))) ⁻¹)
                                                       (annotate-bot e₁))
                                                (subst (λ z → unᵐ-β z ≤ p₂)
                                                       (if-false (false→so! ⦃ <-reflects {m = asize c₁} ⦄ <-irr) ⁻¹
                                                                  )
                                                       (has-bot p₂))
                                                (subst (λ q → annotate q c₂ ≤ⁱ a₂) (p₄₂ ⁻¹) $ subst (_≤ⁱ a₂) (p₄₁ ⁻¹) le)
                                                (subst (λ z → unᵐ-β z ≤ q)
                                                       (( if-true ( true→so! ⦃ <-reflects {m = asize c₁} ⦄
                                                                             (<-+-r <-ascend))
                                                        ∙ if-false ( false→so! ⦃ <-reflects ⦄
                                                                               ((≤→≯ $ =→≤ (  +-cancel-∸-r (asize c₂) (asize c₁) ⁻¹
                                                                                            ∙ ap (_∸ asize c₁) (+-comm (asize c₂) (asize c₁))))))) ⁻¹)
                                                       (has-bot q))))
                                          .snd .snd .snd .fst)
                          (↓-is-sup q .least q'
                             λ where (b' , le) →
                                        let bf₅ = single-at b' (2 + asize c₁ + asize c₂)
                                            p₅ = ap unᵐ-β (if-true (true→so! ⦃ Reflects-ℕ-Path {m = asize c₁ + asize c₂} ⦄ refl))
                                          in
                                        subst (_≤ q') p₅ $
                                        (ite-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₅
                                           , ite-≤ⁱ-intro2 refl eq₀ (has-bot p₁)
                                                (subst (_≤ⁱ a₁)
                                                       (annotate-ext λ n lt → ap unᵐ-β (if-false (false→so! ⦃ Reflects-ℕ-Path ⦄
                                                                                                            (contra
                                                                                                               (λ e → ≤-peel (≤ⁿ-trans (s≤s (≤-suc-r ≤-+-r))
                                                                                                                                       (=→≤ (e ∙ +-comm n 1))))
                                                                                                               (<→≱ $ lt)))) ⁻¹)
                                                       (annotate-bot e₁))
                                                (subst (λ z → unᵐ-β z ≤ p₂)
                                                       (if-false ( false→so! ⦃ Reflects-ℕ-Path ⦄
                                                                             (λ p → false! ⦃ Reflects-id≠+-suc ⦄ ((+-suc-r (asize c₁) (asize c₂) ∙ p) ⁻¹))) ⁻¹)
                                                       (has-bot p₂))
                                                (subst (_≤ⁱ a₂)
                                                       (annotate-ext λ n lt → ap unᵐ-β (if-false (false→so! ⦃ Reflects-ℕ-Path ⦄
                                                                                                            (contra
                                                                                                               (λ e → =→≤ (+-cancel-r (asize c₂) n (2 + asize c₁)
                                                                                                                             (+-comm (asize c₂) (2 + asize c₁) ∙ e)))
                                                                                                               (<→≱ $ lt)))) ⁻¹)
                                                       (annotate-bot e₂))
                                                (subst (_≤ q) (p₅ ⁻¹) le)))
                                          .snd .snd .snd .snd)
    }
  anc-↓-is-sup (While b c) (a , eq) =
    let (inv₀ , p₀ , a₀ , q₀ , eq₀ , e₀) = strip-while eq
        ih = anc-↓-is-sup c (a₀ , e₀)
      in
    record {
      fam≤lub = λ where (bf , le) →
                           let (le1 , le2 , le3 , le4) = while-≤ⁱ-elim2 refl eq₀ le in
                           while-≤ⁱ-intro2 refl eq₀ le1 le2
                             (ih .fam≤lub (shl bf 2 , le3))
                             le4
    ; least = λ where (a'' , eq'') f →
                        let (inv₀' , p₀' , a₀' , q₀' , eq₀' , e₀') = strip-while eq'' in
                        while-≤ⁱ-intro2 eq₀ eq₀'
                          (↓-is-sup inv₀ .least inv₀'
                             λ where (b' , le) →
                                        let bf₁ = single-at b' 0 in
                                        (while-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₁
                                           , while-≤ⁱ-intro2 refl eq₀ le
                                                (has-bot p₀)
                                                (subst (λ q → annotate q c ≤ⁱ a₀)
                                                       (shl-single-at-not {n = 0} {m = 2} z<s ⁻¹)
                                                       (annotate-bot e₀))
                                                (has-bot q₀)))
                                         .fst)
                          (↓-is-sup p₀ .least p₀'
                             λ where (b' , le) →
                                       let bf₂ = single-at b' 1 in
                                       (while-≤ⁱ-elim2 refl eq₀' $
                                        f ( bf₂
                                          , while-≤ⁱ-intro2 refl eq₀
                                              (has-bot inv₀)
                                              le
                                              (subst (λ q → annotate q c ≤ⁱ a₀)
                                                       (shl-single-at-not {n = 1} {m = 2} (s<s z<s) ⁻¹)
                                                       (annotate-bot e₀))
                                              (has-bot q₀)))
                                        .snd .fst)
                          (ih .least (a₀' , e₀')
                              λ where (bf , le) →
                                       let bf₃ = shr (filt bf (_<? asize c)) 2
                                           p₃₁ = annotate-β-filt (λ n lt → true→so! ⦃ <-reflects ⦄ lt)
                                           p₃₂ = shl-shr {f = filt bf (_<? asize c)} {n = 2}
                                         in
                                        subst (_≤ⁱ a₀') p₃₁ $ subst (λ q → annotate q c ≤ⁱ a₀') p₃₂ $
                                        (while-≤ⁱ-elim2 refl eq₀' $
                                         f ( bf₃
                                           , while-≤ⁱ-intro2 refl eq₀
                                               (has-bot inv₀)
                                               (has-bot p₀)
                                               (subst (λ q → annotate q c ≤ⁱ a₀) (p₃₂ ⁻¹) $ subst (_≤ⁱ a₀) (p₃₁ ⁻¹) le)
                                               (subst (λ z → unᵐ-β z ≤ q₀)
                                                      (if-false (false→so! ⦃ <-reflects {m = asize c} ⦄ <-irr ) ⁻¹)
                                                      (has-bot q₀))
                                           ))
                                        .snd .snd .fst)
                          (↓-is-sup q₀ .least q₀'
                             λ where (b' , le) →
                                       let bf₄ = single-at b' (2 + asize c)
                                           p₄ = ap unᵐ-β (if-true (true→so! ⦃ Reflects-ℕ-Path {m = asize c} ⦄ refl))
                                         in
                                       subst (_≤ q₀') p₄ $
                                       (while-≤ⁱ-elim2 refl eq₀' $
                                        f ( bf₄
                                          , while-≤ⁱ-intro2 refl eq₀
                                              (has-bot inv₀)
                                              (has-bot p₀)
                                              (subst (_≤ⁱ a₀)
                                                     (annotate-ext λ n lt → ap unᵐ-β (if-false (false→so! ⦃ Reflects-ℕ-Path ⦄
                                                                                                           (contra
                                                                                                             (λ e → =→≤ (+-inj-r (asize c) n 2 (+-comm (asize c) 2 ∙ e)))
                                                                                                             (<→≱ $ lt)))) ⁻¹)
                                                     (annotate-bot e₀))
                                              (subst (_≤ q₀) (p₄ ⁻¹) le)))
                                       .snd .snd .snd)
    }

{-
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
-}
