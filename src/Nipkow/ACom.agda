module Nipkow.ACom where

open import Prelude
open import Data.Empty
open import Data.Bool renaming (_==_ to _==ᵇ_ ; ==-reflects to ==ᵇ-reflects)
open import Data.Nat renaming (_==_ to _==ⁿ_ ; ==-reflects to ==ⁿ-reflects)
open import Data.Nat.Order.Base renaming (_≤_ to _≤ⁿ_ ; _<_ to _<ⁿ_)
open import Data.String
open import Data.Maybe renaming (rec to recᵐ ; elim to elimᵐ)
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Reflects renaming (dmap to dmapʳ)

open import List1
open import Nipkow.Lang

private variable
  ℓ : Level
  A : 𝒰 ℓ

{- Annotated commands -}

data AnInstr (A : 𝒰 ℓ) : 𝒰 ℓ where
  AnSkip   : (p : A) → AnInstr A
  AnAssign : (x : String) → (e : AExpr) → (p : A) → AnInstr A
  AnSeq    : (c₁ : AnInstr A) → (c₂ : AnInstr A) → AnInstr A
  AnITE    : (b : BExpr) → (p₁ : A) → (c₁ : AnInstr A) → (p₂ : A) → (c₂ : AnInstr A) → (q : A) → AnInstr A
  AnWhile  : (inv : A) → (b : BExpr) → (p : A)  → (c : AnInstr A) → (q : A) → AnInstr A

module AnInstrCode where
  Code-AnInstr : AnInstr A → AnInstr A → 𝒰 (level-of-type A)
  Code-AnInstr     (AnSkip p₁)                (AnSkip p₂)                = p₁ ＝ p₂
  Code-AnInstr     (AnAssign x₁ e₁ p₁)        (AnAssign x₂ e₂ p₂)        = (x₁ ＝ x₂) × (e₁ ＝ e₂) × (p₁ ＝ p₂)
  Code-AnInstr     (AnSeq c₁ c₂)              (AnSeq c₃ c₄)              = Code-AnInstr c₁ c₃ × Code-AnInstr c₂ c₄
  Code-AnInstr     (AnITE b₁ p₁ c₁ p₂ c₂ q₁)  (AnITE b₂ p₃ c₃ p₄ c₄ q₂)  =
    (b₁ ＝ b₂) × (p₁ ＝ p₃) × Code-AnInstr c₁ c₃ × (p₂ ＝ p₄) × Code-AnInstr c₂ c₄ × (q₁ ＝ q₂)
  Code-AnInstr     (AnWhile inv₁ b₁ p₁ c₁ q₁) (AnWhile inv₂ b₂ p₂ c₂ q₂) =
    (inv₁ ＝ inv₂) × (b₁ ＝ b₂) × (p₁ ＝ p₂) × Code-AnInstr c₁ c₂ × (q₁ ＝ q₂)
  Code-AnInstr {A}  _                           _                         = Lift (level-of-type A) ⊥

  code-aninstr-refl : (c : AnInstr A) → Code-AnInstr c c
  code-aninstr-refl (AnSkip p)              = refl
  code-aninstr-refl (AnAssign x e p)        = refl , refl , refl
  code-aninstr-refl (AnSeq c₁ c₂)           = code-aninstr-refl c₁ , code-aninstr-refl c₂
  code-aninstr-refl (AnITE b p₁ c₁ p₂ c₂ q) = refl , refl , code-aninstr-refl c₁ , refl , code-aninstr-refl c₂ , refl
  code-aninstr-refl (AnWhile inv b p c q)   = refl , refl , refl , code-aninstr-refl c , refl

  encode-aninstr : ∀ {c₁ c₂ : AnInstr A} → c₁ ＝ c₂ → Code-AnInstr c₁ c₂
  encode-aninstr {c₁} e = subst (Code-AnInstr c₁) e (code-aninstr-refl c₁)

  decode-aninstr : ∀ {c₁ c₂ : AnInstr A} → Code-AnInstr c₁ c₂ → c₁ ＝ c₂
  decode-aninstr {c₁ = AnSkip p₁}                {AnSkip p₂}                 cd                                 = ap AnSkip cd
  decode-aninstr {c₁ = AnAssign x₁ e₁ p₁}        {AnAssign x₂ e₂ p₂}        (cd₁ , cd₂ , cd₃)                   =
    ap (λ q → AnAssign q e₁ p₁) cd₁ ∙ ap² (AnAssign x₂) cd₂ cd₃
  decode-aninstr {c₁ = AnSeq c₁ c₂}              {AnSeq c₃ c₄}              (cd₁ , cd₂)                         =
    ap² AnSeq (decode-aninstr cd₁) (decode-aninstr cd₂)
  decode-aninstr {c₁ = AnITE b₁ p₁ c₁ p₂ c₂ q₁}  {AnITE b₂ p₃ c₃ p₄ c₄ q₂}  (cd₁ , cd₂ , cd₃ , cd₄ , cd₅ , cd₆) =
    ap² (λ z₁ z₂ → AnITE z₁ z₂ c₁ p₂ c₂ q₁) cd₁ cd₂
    ∙ ap² (λ z₁ z₂ → AnITE b₂ p₃ z₁ z₂ c₂ q₁) (decode-aninstr cd₃) cd₄
    ∙ ap² (AnITE b₂ p₃ c₃ p₄) (decode-aninstr cd₅) cd₆
  decode-aninstr {c₁ = AnWhile inv₁ b₁ p₁ c₁ q₁} {AnWhile inv₂ b₂ p₂ c₂ q₂} (cd₁ , cd₂ , cd₃ , cd₄ , cd₅)       =
    ap (λ z → AnWhile z b₁ p₁ c₁ q₁) cd₁
    ∙ ap² (λ z₁ z₂ → AnWhile inv₂ z₁ z₂ c₁ q₁) cd₂ cd₃
    ∙ ap² (AnWhile inv₂ b₂ p₂) (decode-aninstr cd₄) cd₅

AnSkip-inj : ∀ {p₁ p₂ : A} → AnSkip p₁ ＝ AnSkip p₂ → p₁ ＝ p₂
AnSkip-inj = AnInstrCode.encode-aninstr

AnAssign-inj : ∀ {x e y g} {p q : A} → AnAssign x e p ＝ AnAssign y g q → (x ＝ y) × (e ＝ g) × (p ＝ q)
AnAssign-inj = AnInstrCode.encode-aninstr

AnSeq-inj : ∀ {c₁ c₂ c₃ c₄ : AnInstr A} → AnSeq c₁ c₂ ＝ AnSeq c₃ c₄ → (c₁ ＝ c₃) × (c₂ ＝ c₄)
AnSeq-inj e = let (h1 , h2) = AnInstrCode.encode-aninstr e in
              AnInstrCode.decode-aninstr h1 , AnInstrCode.decode-aninstr h2

AnITE-inj : ∀ {b₁ b₂ c₁ c₂ c₃ c₄} {p₁ p₂ p₃ p₄ q₁ q₂ : A}
          → AnITE b₁ p₁ c₁ p₂ c₂ q₁ ＝ AnITE b₂ p₃ c₃ p₄ c₄ q₂
          → (b₁ ＝ b₂) × (p₁ ＝ p₃) × (c₁ ＝ c₃) × (p₂ ＝ p₄) × (c₂ ＝ c₄) × (q₁ ＝ q₂)
AnITE-inj e = let (h1 , h2 , h3 , h4 , h5 , h6) = AnInstrCode.encode-aninstr e in
              h1 , h2 , AnInstrCode.decode-aninstr h3 , h4 , AnInstrCode.decode-aninstr h5 , h6

AnWhile-inj : ∀ {b₁ b₂ c₁ c₂} {inv₁ inv₂ p₁ p₂ q₁ q₂ : A}
          → AnWhile inv₁ b₁ p₁ c₁ q₁ ＝ AnWhile inv₂ b₂ p₂ c₂ q₂
          → (inv₁ ＝ inv₂) × (b₁ ＝ b₂) × (p₁ ＝ p₂) × (c₁ ＝ c₂) × (q₁ ＝ q₂)
AnWhile-inj e = let (h1 , h2 , h3 , h4 , h5) = AnInstrCode.encode-aninstr e in
                h1 , h2 , h3 , AnInstrCode.decode-aninstr h4 , h5

AnSkip≠AnAssign : ∀ {x e} {p q : A} → AnSkip p ≠ AnAssign x e q
AnSkip≠AnAssign = lower ∘ AnInstrCode.encode-aninstr

AnSkip≠AnSeq : ∀ {c₁ c₂} {q : A} → AnSkip q ≠  AnSeq c₁ c₂
AnSkip≠AnSeq = lower ∘ AnInstrCode.encode-aninstr

AnSkip≠AnITE : ∀ {b c₁ c₂} {p₁ p₂ q r : A} → AnSkip r ≠ AnITE b p₁ c₁ p₂ c₂ q
AnSkip≠AnITE = lower ∘ AnInstrCode.encode-aninstr

AnSkip≠AnWhile : ∀ {b c} {inv p q r : A} → AnSkip r ≠ AnWhile inv b p c q
AnSkip≠AnWhile = lower ∘ AnInstrCode.encode-aninstr

AnAssign≠AnSeq : ∀ {x e c₁ c₂} {p : A} → AnAssign x e p ≠ AnSeq c₁ c₂
AnAssign≠AnSeq = lower ∘ AnInstrCode.encode-aninstr

AnAssign≠AnITE : ∀ {b c₁ c₂ x e} {p₁ p₂ q r : A} → AnAssign x e r ≠ AnITE b p₁ c₁ p₂ c₂ q
AnAssign≠AnITE = lower ∘ AnInstrCode.encode-aninstr

AnAssign≠AnWhile : ∀ {b c x e} {inv p q r : A} → AnAssign x e r ≠ AnWhile inv b p c q
AnAssign≠AnWhile = lower ∘ AnInstrCode.encode-aninstr

AnSeq≠AnITE : ∀ {b c₁ c₂ c₃ c₄} {p₁ p₂ q : A} → AnSeq c₁ c₂ ≠ AnITE b p₁ c₃ p₂ c₄ q
AnSeq≠AnITE = lower ∘ AnInstrCode.encode-aninstr

AnSeq≠AnWhile : ∀ {b c₁ c₂ c} {inv p q : A} → AnSeq c₁ c₂ ≠ AnWhile inv b p c q
AnSeq≠AnWhile = lower ∘ AnInstrCode.encode-aninstr

AnITE≠AnWhile : ∀ {b₁ c₁ c₂ b₂ c₄} {p₁ p₂ q₁ inv p₃ q₂ : A} → AnITE b₁ p₁ c₁ p₂ c₂ q₁ ≠ AnWhile inv b₂ p₃ c₄ q₂
AnITE≠AnWhile = lower ∘ AnInstrCode.encode-aninstr

-- annotation ops

shift : (ℕ → A) → ℕ → ℕ → A
shift f n k = f (k + n)

annotate : (ℕ → A) → Instr → AnInstr A
annotate f  Skip         = AnSkip (f 0)
annotate f (Assign x e)  = AnAssign x e (f 0)
annotate f (Seq c₁ c₂)   = AnSeq (annotate f c₁) (annotate (shift f (isize c₁)) c₂)
annotate f (ITE b c₁ c₂) = AnITE b
                             (f 0) (annotate (shift f 1) c₁)
                             (f (suc (isize c₁))) (annotate (shift f (2 + isize c₁)) c₂)
                             (f (2 + isize c₁ + isize c₂))
annotate f (While b c)   = AnWhile (f 0) b (f 1) (annotate (shift f 2) c) (f (2 + isize c))

annotate-ext : ∀ {c : Instr} {f g : ℕ → A}
             → (∀ n → n <ⁿ isize c → f n ＝ g n)
             → annotate f c ＝ annotate g c
annotate-ext {c = Skip}                h = ap AnSkip (h 0 z<s)
annotate-ext {c = Assign x e}          h = ap (AnAssign x e) (h 0 z<s)
annotate-ext {c = Seq c₁ c₂}           h = ap² AnSeq (annotate-ext λ n lt → h n (<-≤-trans lt ≤-+-r))
                                                     (annotate-ext λ n lt → h (n + isize c₁)
                                                                              (≤-<-trans (=→≤ (+-comm n (isize c₁))) (<≃<+l $ lt)))
annotate-ext {c = ITE b c₁ c₂} {f} {g} h =    ap² (λ x y → AnITE b x y (f (suc (isize c₁)))
                                                                       (annotate (shift f (2 + isize c₁)) c₂)
                                                                       (f (2 + isize c₁ + isize c₂)))
                                                  (h 0 z<s)
                                                  (annotate-ext λ n lt → h (n + 1) (≤-<-trans (=→≤ (+-comm n 1))
                                                                                      (s<s (<-≤-trans lt
                                                                                              (≤-trans ≤-+-r
                                                                                                (=→≤ (  +-assoc (isize c₁) 2 (isize c₂)
                                                                                                      ∙ ap (_+ isize c₂) (+-comm (isize c₁) 2))))))))
                                            ∙ ap² (λ x y → AnITE b (g 0) (annotate (shift g 1) c₁) x y (f (2 + isize c₁ + isize c₂)))
                                                  (h (suc (isize c₁)) (s<s (<-≤-trans (≤-<-trans (=→≤ (+-zero-r (isize c₁) ⁻¹))
                                                                                                 (<≃<+l $ z<s))
                                                                                       (  =→≤ (+-assoc (isize c₁) 2 (isize c₂)
                                                                                        ∙ ap (_+ isize c₂) (+-comm (isize c₁) 2))))))
                                                  (annotate-ext λ n lt → h (n + (2 + isize c₁)) (<-trans (<≃<+r $ lt)
                                                                                                   (≤-<-trans (=→≤ (+-comm (isize c₂) (2 + isize c₁)))
                                                                                                      <-ascend)))
                                            ∙ ap (AnITE b (g 0) (annotate (shift g 1) c₁) (g (suc (isize c₁)))
                                                                (annotate (shift g (2 + isize c₁)) c₂))
                                                 (h (2 + isize c₁ + isize c₂) (s<s (s<s <-ascend)))
annotate-ext {c = While b c}   {f} {g} h =   ap² (λ x y → AnWhile x b y (annotate (shift f 2) c) (f (2 + isize c)))
                                                 (h 0 z<s)
                                                 (h 1 (s<s z<s))
                                           ∙ ap² (AnWhile (g 0) b (g 1))
                                                 (annotate-ext λ n lt → h (n + 2) (<-trans (<≃<+r $ lt)
                                                                                     (≤-<-trans (=→≤ (+-comm (isize c) 2))
                                                                                                (s<s (s<s <-ascend)))))
                                                 (h (2 + isize c) (s<s (s<s <-ascend)))

annos : AnInstr A → List1 A
annos (AnSkip p)              = [ p ]₁
annos (AnAssign _ _ p)        = [ p ]₁
annos (AnSeq c₁ c₂)           = annos c₁ ++₁ annos c₂
annos (AnITE _ p₁ c₁ p₂ c₂ q) = ((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) ∶+₁ q
annos (AnWhile inv _ p c q)   = (inv ∷₁ (p ∷₁ annos c)) ∶+₁ q

post : AnInstr A → A
post = List1.last ∘ annos

strip : AnInstr A → Instr
strip (AnSkip _)            = Skip
strip (AnAssign x e _)      = Assign x e
strip (AnSeq c₁ c₂)         = Seq (strip c₁) (strip c₂)
strip (AnITE b _ c₁ _ c₂ _) = ITE b (strip c₁) (strip c₂)
strip (AnWhile _ b _ c _)   = While b (strip c)

strip-annotate : ∀ {f : ℕ → A} {c} → strip (annotate f c) ＝ c
strip-annotate {c = Skip}        = refl
strip-annotate {c = Assign x e}  = refl
strip-annotate {c = Seq c₁ c₂}   = ap² Seq (strip-annotate {c = c₁}) (strip-annotate {c = c₂})
strip-annotate {c = ITE b c₁ c₂} = ap² (ITE b) (strip-annotate {c = c₁}) (strip-annotate {c = c₂})
strip-annotate {c = While b c}   = ap (While b) (strip-annotate {c = c})

annos-annotate-const : ∀ {a : A} {c} → annos (annotate (λ _ → a) c) ＝ replicate₁ (isize c) a
annos-annotate-const {c = Skip}        = refl
annos-annotate-const {c = Assign x e}  = refl
annos-annotate-const {c = Seq c₁ c₂}   =   ap² (_++₁_) (annos-annotate-const {c = c₁})
                                                       (annos-annotate-const {c = c₂})
                                         ∙ replicate₁-+ (isize-pos c₁) (isize-pos c₂) ⁻¹
annos-annotate-const {c = ITE b c₁ c₂} = {!!}
annos-annotate-const {c = While b c}   = {!!}

length-annos-same : ∀ {c₁ c₂ : AnInstr A}
                  → is-true (strip c₁ ==ⁱ strip c₂)
                  → length₁ (annos c₁) ＝ length₁ (annos c₂)
length-annos-same {c₁ = AnSkip p₁}                {c₂ = AnSkip p₂}                eq = refl
length-annos-same {c₁ = AnAssign x₁ e₁ p₁}        {c₂ = AnAssign x₂ e₂ p₂}        eq = refl
length-annos-same {c₁ = AnSeq c₁ c₂}              {c₂ = AnSeq c₃ c₄}              eq =
  let h12 = and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = strip c₂ ==ⁱ strip c₄} $ eq in
    length₁-++ {xs = annos c₁} {ys = annos c₂}
  ∙ ap² _+_ (length-annos-same {c₁ = c₁} (h12 .fst))
            (length-annos-same {c₁ = c₂} (h12 .snd))
  ∙ length₁-++ {xs = annos c₃} {ys = annos c₄} ⁻¹
length-annos-same {c₁ = AnITE b₁ p₁ c₁ p₂ c₂ q₁}  {c₂ = AnITE b₂ p₃ c₃ p₄ c₄ q₂}  eq =
  let h12 = and-true-≃ {x = strip c₁ ==ⁱ strip c₃} {y = strip c₂ ==ⁱ strip c₄} $
            (and-true-≃ {x = b₁ ==ᵇᵉ b₂} {y = strip c₁ ==ⁱ strip c₃ and strip c₂ ==ⁱ strip c₄} $ eq) .snd in
  ap suc (  length-to-list {xs = (p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)}
          ∙ length₁-++ {xs = p₁ ∷₁ annos c₁} {ys = p₂ ∷₁ annos c₂}
          ∙ ap² _+_ (ap suc (length-annos-same {c₁ = c₁} (h12 .fst)))
                    (ap suc (length-annos-same {c₁ = c₂} (h12 .snd)))
          ∙ length₁-++ {xs = p₃ ∷₁ annos c₃} {ys = p₄ ∷₁ annos c₄} ⁻¹
          ∙ length-to-list {xs = (p₃ ∷₁ annos c₃) ++₁ (p₄ ∷₁ annos c₄)} ⁻¹)
length-annos-same {c₁ = AnWhile inv₁ b₁ p₁ c₁ q₁} {c₂ = AnWhile inv₂ b₂ p₂ c₂ q₂} eq =
  let h = (and-true-≃ {x = b₁ ==ᵇᵉ b₂} {y = strip c₁ ==ⁱ strip c₂} $ eq) .snd in
  ap suc (  length-to-list {xs = inv₁ ∷₁ (q₁ ∷₁ annos c₁)}
          ∙ ap (2 +_) (length-annos-same {c₁ = c₁} h)
          ∙ length-to-list {xs = inv₂ ∷₁ (q₂ ∷₁ annos c₂)} ⁻¹)

strip-annos-same : ∀ {a b : AnInstr A}
                 → is-true (strip a ==ⁱ strip b)
                 → annos a ＝ annos b
                 → a ＝ b
strip-annos-same {a = AnSkip p₁}                {b = AnSkip p₂}                eqs eqa = ap AnSkip (∶+-inj eqa .snd)
strip-annos-same {a = AnAssign x e₁ p₁}         {b = AnAssign y e₂ p₂}         eqs eqa =
  let h = and-true-≃ {x = ⌊ x ≟ y ⌋} {y = e₁ ==ᵃᵉ e₂} $ eqs in
    ap² (λ x y → AnAssign x y p₁) (true-reflects discrete-reflects! (h .fst))
                                  (true-reflects (reflects-aexpr e₁ e₂) (h .snd))
  ∙ ap (AnAssign y e₂) (∶+-inj eqa .snd)
strip-annos-same {a = AnSeq a₁ a₂}              {b = AnSeq b₁ b₂}              eqs eqa =
  let h = and-true-≃ {x = strip a₁ ==ⁱ strip b₁} {y = strip a₂ ==ⁱ strip b₂} $ eqs
      h2 = ++₁-same-inj (length-annos-same {c₁ = a₁} (h .fst)) eqa
    in
  ap² AnSeq (strip-annos-same (h .fst) (h2 .fst)) (strip-annos-same (h .snd) (h2 .snd))
strip-annos-same {a = AnITE b₁ p₁ a₁ p₂ a₂ q₁}  {b = AnITE b₂ p₃ a₃ p₄ a₄ q₂}  eqs eqa =
  let h = and-true-≃ {x = b₁ ==ᵇᵉ b₂} {y = (strip a₁ ==ⁱ strip a₃) and (strip a₂ ==ⁱ strip a₄)} $ eqs
      h2 = and-true-≃ {x = strip a₁ ==ⁱ strip a₃} {y = strip a₂ ==ⁱ strip a₄} $ h .snd
      h3 = ∶+-inj eqa
      h4 = ++₁-same-inj (ap suc (length-annos-same {c₁ = a₁} (h2 .fst))) (to-list-inj (h3 .fst))
      h5 = ∷₁-inj (h4 .fst)
      h6 = ∷₁-inj (h4 .snd)
    in
    ap² (λ x y → AnITE x y a₁ p₂ a₂ q₁) (true-reflects (reflects-bexpr b₁ b₂) (h .fst))
                                        (h5 .fst)
  ∙ ap² (λ x y → AnITE b₂ p₃ x y a₂ q₁) (strip-annos-same (h2 .fst) (h5 .snd)) (h6 .fst)
  ∙ ap² (AnITE b₂ p₃ a₃ p₄) (strip-annos-same (h2 .snd) (h6 .snd)) (h3 .snd)
strip-annos-same {a = AnWhile inv₁ b₁ p₁ a₁ q₁} {b = AnWhile inv₂ b₂ p₂ a₂ q₂} eqs eqa =
  let h = and-true-≃ {x = b₁ ==ᵇᵉ b₂} {y = strip a₁ ==ⁱ strip a₂} $ eqs
      h2 = ∶+-inj eqa
      h3 = ∷₁-inj (to-list-inj (h2 .fst))
      h4 = ∷₁-inj (h3 .snd)
    in
    ap² (λ x y → AnWhile x y p₁ a₁ q₁) (h3 .fst) (true-reflects (reflects-bexpr b₁ b₂) (h .fst))
  ∙ ap² (λ x y → AnWhile inv₂ b₂ x y q₁) (h4 .fst) (strip-annos-same (h .snd) (h4 .snd))
  ∙ ap (AnWhile inv₂ b₂ p₂ a₂) (h2 .snd)

-- case reflection

opaque
  reflects-strip-skip : ∀ c → Reflects (Σ[ p ꞉ A ] (c ＝ AnSkip p))
                                       (Skip ==ⁱ strip c)
  reflects-strip-skip (AnSkip p)              = ofʸ (p , refl)
  reflects-strip-skip (AnAssign x e p)        = ofⁿ λ where (q , eq) → AnSkip≠AnAssign (eq ⁻¹)
  reflects-strip-skip (AnSeq c₁ c₂)           = ofⁿ λ where (q , eq) → AnSkip≠AnSeq (eq ⁻¹)
  reflects-strip-skip (AnITE b p₁ c₁ p₂ c₂ q) = ofⁿ λ where (q , eq) → AnSkip≠AnITE (eq ⁻¹)
  reflects-strip-skip (AnWhile inv b p c q)   = ofⁿ λ where (q , eq) → AnSkip≠AnWhile (eq ⁻¹)

  strip-skip-r : ∀ {c} → strip c ＝ Skip → Σ[ p ꞉ A ] (c ＝ AnSkip p)
  strip-skip-r {c} eq =
    true-reflects (reflects-strip-skip c) $
    reflects-true (reflects-instr Skip (strip c)) (eq ⁻¹)

  reflects-strip-assign : ∀ {x e} c
                        → Reflects (Σ[ p ꞉ A ] (c ＝ AnAssign x e p))
                                   (Assign x e ==ⁱ strip c)
  reflects-strip-assign         (AnSkip p)             = ofⁿ λ where (q , eq) → AnSkip≠AnAssign eq
  reflects-strip-assign {x} {e} (AnAssign y g p)       =
    dmapʳ (λ where (eq1 , eq2) → p , ap² (λ z₁ z₂ → AnAssign z₁ z₂ p) (eq1 ⁻¹) (eq2 ⁻¹))
          (_∘ λ where (q , eq) → let (h1 , h2 , _) = AnAssign-inj eq in h1 ⁻¹ , h2 ⁻¹)
          (reflects-and2 (discrete-reflects! {x = x} {y = y}) (reflects-aexpr e g))
  reflects-strip-assign         (AnSeq c₁ c₂)          = ofⁿ λ where (q , eq) → AnAssign≠AnSeq (eq ⁻¹)
  reflects-strip-assign         (AnITE b p₁ c p₂ c₁ q) = ofⁿ λ where (q , eq) → AnAssign≠AnITE (eq ⁻¹)
  reflects-strip-assign         (AnWhile inv b p c q)  = ofⁿ λ where (q , eq) → AnAssign≠AnWhile (eq ⁻¹)

  strip-assign-r : ∀ {x e c} → strip c ＝ Assign x e → Σ[ p ꞉ A ] (c ＝ AnAssign x e p)
  strip-assign-r {x} {e} {c} eq =
    true-reflects (reflects-strip-assign c) $
    reflects-true (reflects-instr (Assign x e) (strip c)) (eq ⁻¹)

  reflects-strip-seq : ∀ {A : 𝒰 ℓ} {c₁ c₂ : Instr} c
                     → Reflects (Σ[ a₁ ꞉ AnInstr A ] Σ[ a₂ ꞉ AnInstr A ]
                                       (c ＝ AnSeq a₁ a₂)
                                     × (strip a₁ ＝ c₁) × (strip a₂ ＝ c₂))
                                (Seq c₁ c₂ ==ⁱ strip c)
  reflects-strip-seq           (AnSkip p)              = ofⁿ λ where (a₁ , a₂ , eq₁ , eq₂ , eq₃) → AnSkip≠AnSeq eq₁
  reflects-strip-seq           (AnAssign x e p)        = ofⁿ λ where (a₁ , a₂ , eq₁ , eq₂ , eq₃) → AnAssign≠AnSeq eq₁
  reflects-strip-seq {c₁} {c₂} (AnSeq c₃ c₄)           =
    dmapʳ (λ where (eq1 , eq2) →
                      c₃ , c₄ , refl , eq1 ⁻¹ , eq2 ⁻¹)
          (_∘ λ where (a₁ , a₂ , eq₁ , eq₂ , eq₃) →
                        let (eq3 , eq4) = AnSeq-inj eq₁ in
                        (ap strip eq3 ∙ eq₂) ⁻¹ , (ap strip eq4 ∙ eq₃) ⁻¹)
          (reflects-and2 (reflects-instr c₁ (strip c₃)) (reflects-instr c₂ (strip c₄)))
  reflects-strip-seq           (AnITE b p₁ c₃ p₂ c₄ q) = ofⁿ λ where (a₁ , a₂ , eq₁ , eq₂ , eq₃) → AnSeq≠AnITE (eq₁ ⁻¹)
  reflects-strip-seq           (AnWhile inv b p c₃ q)  = ofⁿ λ where (a₁ , a₂ , eq₁ , eq₂ , eq₃) → AnSeq≠AnWhile (eq₁ ⁻¹)

  strip-seq-r : ∀ {A : 𝒰 ℓ} {c₁ c₂ c}
              → strip c ＝ Seq c₁ c₂
              → Σ[ a₁ ꞉ AnInstr A ] Σ[ a₂ ꞉ AnInstr A ]
                   (c ＝ AnSeq a₁ a₂)
                 × (strip a₁ ＝ c₁) × (strip a₂ ＝ c₂)
  strip-seq-r {c₁} {c₂} {c} eq =
    true-reflects (reflects-strip-seq c) $
    reflects-true (reflects-instr (Seq c₁ c₂) (strip c)) (eq ⁻¹)

  reflects-strip-ite : ∀ {A : 𝒰 ℓ} {b c₁ c₂} c
                     → Reflects (Σ[ p₁ ꞉ A ] Σ[ a₁ ꞉ AnInstr A ] Σ[ p₂ ꞉ A ] Σ[ a₂ ꞉ AnInstr A ] Σ[ q ꞉ A ]
                                      (c ＝ AnITE b p₁ a₁ p₂ a₂ q)
                                    × (strip a₁ ＝ c₁) × (strip a₂ ＝ c₂))
                                (ITE b c₁ c₂ ==ⁱ strip c)
  reflects-strip-ite               (AnSkip p)               =
    ofⁿ λ where (p₁ , a₁ , p₂ , a₂ , q , eq₁ , eq₂ , eq₃) → AnSkip≠AnITE eq₁
  reflects-strip-ite               (AnAssign x e p)         =
    ofⁿ λ where (p₁ , a₁ , p₂ , a₂ , q , eq₁ , eq₂ , eq₃) → AnAssign≠AnITE eq₁
  reflects-strip-ite               (AnSeq c₃ c₄)            =
    ofⁿ λ where (p₁ , a₁ , p₂ , a₂ , q , eq₁ , eq₂ , eq₃) → AnSeq≠AnITE eq₁
  reflects-strip-ite {b} {c₁} {c₂} (AnITE b₂ p₁ c₃ p₂ c₄ q) =
    dmapʳ (λ where (eq1 , eq2 , eq3) →
                        p₁ , c₃ , p₂ , c₄ , q , ap (λ z → AnITE z p₁ c₃ p₂ c₄ q) (eq1 ⁻¹) , eq2 ⁻¹ , eq3 ⁻¹)
          (_∘ λ where (p₁ , a₁ , p₂ , a₂ , q , eq₁ , eq₂ , eq₃) →
                        let (h1 , _ , h3 , _ , h5 , _) = AnITE-inj eq₁ in
                          h1 ⁻¹ , (ap strip h3 ∙ eq₂) ⁻¹ , (ap strip h5 ∙ eq₃) ⁻¹)
          (reflects-and3 (reflects-bexpr b b₂) (reflects-instr c₁ (strip c₃)) (reflects-instr c₂ (strip c₄)))
  reflects-strip-ite               (AnWhile inv b p c₃ q)   =
    ofⁿ λ where (p₁ , a₁ , p₂ , a₂ , q , eq₁ , eq₂ , eq₃) → AnITE≠AnWhile (eq₁ ⁻¹)

  strip-ite-r : ∀ {A : 𝒰 ℓ} {b c₁ c₂ c}
              → strip c ＝ ITE b c₁ c₂
              → Σ[ p₁ ꞉ A ] Σ[ a₁ ꞉ AnInstr A ] Σ[ p₂ ꞉ A ] Σ[ a₂ ꞉ AnInstr A ] Σ[ q ꞉ A ]
                     (c ＝ AnITE b p₁ a₁ p₂ a₂ q)
                   × (strip a₁ ＝ c₁) × (strip a₂ ＝ c₂)
  strip-ite-r {b} {c₁} {c₂} {c} eq =
    true-reflects (reflects-strip-ite c) $
    reflects-true (reflects-instr (ITE b c₁ c₂) (strip c)) (eq ⁻¹)

  reflects-strip-while : ∀ {A : 𝒰 ℓ} {b c₀} c
                       → Reflects (Σ[ inv ꞉ A ] Σ[ p ꞉ A ] Σ[ a ꞉ AnInstr A ] Σ[ q ꞉ A ]
                                        (c ＝ AnWhile inv b p a q)
                                      × (strip a ＝ c₀))
                                  (While b c₀ ==ⁱ strip c)
  reflects-strip-while          (AnSkip p)              = ofⁿ λ where (inv , q , a , r , eq₁ , eq₂) → AnSkip≠AnWhile eq₁
  reflects-strip-while          (AnAssign x e p)        = ofⁿ λ where (inv , q , a , r , eq₁ , eq₂) → AnAssign≠AnWhile eq₁
  reflects-strip-while          (AnSeq c₁ c₂)           = ofⁿ λ where (inv , q , a , r , eq₁ , eq₂) → AnSeq≠AnWhile eq₁
  reflects-strip-while          (AnITE b p₁ c₁ p₂ c₂ q) = ofⁿ λ where (inv , q , a , r , eq₁ , eq₂) → AnITE≠AnWhile eq₁
  reflects-strip-while {b} {c₀} (AnWhile inv b₂ p c q)  =
    dmapʳ (λ where (eq1 , eq2) →
                      inv , p , c , q , ap (λ z → AnWhile inv z p c q) (eq1 ⁻¹) , eq2 ⁻¹)
          (_∘ λ where (inv , q₁ , a , r , eq₁ , eq₂) →
                        let (_ , h2 , _ , h4 , _) = AnWhile-inj eq₁ in
                           h2 ⁻¹ , (ap strip h4 ∙ eq₂) ⁻¹)
          (reflects-and2 (reflects-bexpr b b₂) (reflects-instr c₀ (strip c)))

  strip-while-r : ∀ {A : 𝒰 ℓ} {b c₀ c}
                → strip c ＝ While b c₀
                → Σ[ inv ꞉ A ] Σ[ p ꞉ A ] Σ[ a ꞉ AnInstr A ] Σ[ q ꞉ A ]
                     (c ＝ AnWhile inv b p a q) × (strip a ＝ c₀)
  strip-while-r {b} {c₀} {c} eq =
    true-reflects (reflects-strip-while c) $
    reflects-true (reflects-instr (While b c₀) (strip c)) (eq ⁻¹)

-- subtype of structurally equal annotated commands

AnStr : 𝒰 ℓ → Instr → 𝒰 ℓ
AnStr A c = fibre (strip {A = A}) c
