module Nipkow.Lang where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool renaming (_==_ to _==ᵇ_)
open import Data.Nat renaming (_==_ to _==ⁿ_)
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)

open import List1

private variable
  A : 𝒰

{- The programming language -}

data AExpr : 𝒰 where
  ANum  : ℕ → AExpr
  AVar  : String → AExpr
  APlus : AExpr → AExpr → AExpr

data BExpr : 𝒰 where
  BC   : Bool → BExpr
  BNot : BExpr → BExpr
  BAnd : BExpr → BExpr → BExpr
  BLt  : AExpr → AExpr → BExpr

data Instr : 𝒰 where
  Skip   : Instr
  Assign : String → AExpr → Instr
  Seq    : Instr → Instr → Instr
  ITE    : BExpr → Instr → Instr → Instr
  While  : BExpr → Instr → Instr

af : (String → ℕ) → AExpr → ℕ
af g (ANum n)      = n
af g (AVar x)      = g x
af g (APlus e₁ e₂) = af g e₁ + af g e₂

bf : (String → ℕ) → BExpr → Bool
bf g (BC c)       = c
bf g (BNot b)     = not (bf g b)
bf g (BAnd b₁ b₂) = bf g b₁ and bf g b₂
bf g (BLt e₁ e₂)  = af g e₁ <ᵇ af g e₂

_==ᵃᵉ_ : AExpr → AExpr → Bool
(ANum n)      ==ᵃᵉ (ANum m)      = n ==ⁿ m 
(AVar x)      ==ᵃᵉ (AVar y)      = x =ₛ y
(APlus e₁ e₂) ==ᵃᵉ (APlus e₃ e₄) = e₁ ==ᵃᵉ e₃ and e₂ ==ᵃᵉ e₄
_             ==ᵃᵉ _             = false

_==ᵇᵉ_ : BExpr → BExpr → Bool
(BC c₁)      ==ᵇᵉ (BC c₂)      = c₁ ==ᵇ c₂
(BNot e₁)    ==ᵇᵉ (BNot e₂)    = e₁ ==ᵇᵉ e₂
(BAnd e₁ e₂) ==ᵇᵉ (BAnd e₃ e₄) = e₁ ==ᵇᵉ e₃ and e₂ ==ᵇᵉ e₄
(BLt e₁ e₂)  ==ᵇᵉ (BLt e₃ e₄)  = e₁ ==ᵃᵉ e₃ and e₂ ==ᵃᵉ e₄
_            ==ᵇᵉ _            = false

_==ⁱ_ : Instr → Instr → Bool
Skip           ==ⁱ Skip           = true
(Assign x e₁)  ==ⁱ (Assign y e₂)  = (x =ₛ y) and e₁ ==ᵃᵉ e₂
(Seq x₁ x₂)    ==ⁱ (Seq y₁ y₂)    = x₁ ==ⁱ y₁ and x₂ ==ⁱ y₂
(ITE b₁ x₁ x₂) ==ⁱ (ITE b₂ y₁ y₂) = b₁ ==ᵇᵉ b₂ and x₁ ==ⁱ y₁ and x₂ ==ⁱ y₂
(While b₁ x₁)  ==ⁱ (While b₂ x₂)  = b₁ ==ᵇᵉ b₂ and x₁ ==ⁱ x₂
_              ==ⁱ _              = false

{- Annotated commands -}

data AnInstr (A : 𝒰) : 𝒰 where
  AnSkip   : A → AnInstr A
  AnAssign : String → AExpr → A → AnInstr A
  AnSeq    : AnInstr A → AnInstr A → AnInstr A
  AnITE    : BExpr → A → AnInstr A → A → AnInstr A → A → AnInstr A
  AnWhile  : A → BExpr → A → AnInstr A → A → AnInstr A

annos : AnInstr A → List1 A
annos (AnSkip p)              = [ p ]₁
annos (AnAssign _ _ p)        = [ p ]₁
annos (AnSeq c₁ c₂)           = annos c₁ ++₁ annos c₂
annos (AnITE b p₁ c₁ p₂ c₂ q) = to-list ((p₁ ∷₁ annos c₁) ++₁ (p₂ ∷₁ annos c₂)) +∶ q
annos (AnWhile inv b p c q)   = to-list (inv ∷₁ (q ∷₁ annos c)) +∶ q

post : AnInstr A → A
post = List1.last ∘ annos

strip : AnInstr A → Instr
strip (AnSkip _)            = Skip
strip (AnAssign x e _)      = Assign x e
strip (AnSeq c₁ c₂)         = Seq (strip c₁) (strip c₂)
strip (AnITE b _ c₁ _ c₂ _) = ITE b (strip c₁) (strip c₂)
strip (AnWhile _ b _ c _)   = While b (strip c)
