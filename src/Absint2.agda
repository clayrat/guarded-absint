module Absint2 where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Inductive
open import Data.String
open import Data.Maybe renaming (rec to recᵐ)
open import Data.List
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Lang
open import State

-- TODO merge with AbsInt1

module StateA
  (A : 𝒰)
  (top : A)
  (add : A → A → A)
  (fromN : ℕ → A)

  where

  open State.State A top

  a-af : State → AExpr → A
  a-af s (ANum n)      = fromN n
  a-af s (AVar x)      = stlup s x
  a-af s (APlus e₁ e₂) = add (a-af s e₁) (a-af s e₂)

module AInt2
  (A : 𝒰)
  (top : A)
  (add : A → A → A)
  (fromN : ℕ → A)
  (to-pred : A → AExpr → Assert)
  (learn-from-success : St A → BExpr → Maybe (St A))
  (learn-from-failure : St A → BExpr → Maybe (St A))
  (join : A → A → A)
  (thinner : A → A → Bool)
  (over-approx : ℕ → St A → St A → St A)
  (choose-1 : St A → Instr → ℕ)
  (choose-2 : St A → Instr → ℕ)

  where

  open State.State A top
  open StateA A top add fromN

  -- TODO duplication

  s→a : State → Assert
  s→a []            = QTrue
  s→a ((x , a) ∷ t) = QConj (to-pred a (AVar x)) (s→a t)

  s→a' : Maybe State → Assert
  s→a' (just s) = s→a s
  s→a' nothing  = QFalse

  join-state : State → State → State
  join-state []             s2 = []
  join-state ((x , v) ∷ s1) s2 = stupd x (join v (stlup s2 x)) (join-state s1 s2)

  join-state-m : State → Maybe State → State
  join-state-m s1 (just s2) = join-state s1 s2
  join-state-m s1  nothing  = s1

  mark : Instr → AnInstr
  mark (Assign x e) = AnPre QFalse (AnAssign x e)
  mark (Seq i₁ i₂)  = AnSeq (mark i₁) (mark i₂)
  mark (While b i)  = AnWhile b QFalse (mark i)

  step1 : (State → AnInstr × Maybe State)
        → BExpr → State → State → State
  step1 ab b init s = recᵐ s (λ s′ → join-state-m init (ab s′ .snd)) (learn-from-success s b)

  step2 : (State → AnInstr × Maybe State)
        → BExpr → State → State → ℕ → State
  step2 ab b init s  zero   = s
  step2 ab b init s (suc n) = step2 ab b init (step1 ab b init s) n

  s-stable : State → State → Bool
  s-stable []             s2 = true
  s-stable ((x , v) ∷ s1) s2 = thinner (stlup s2 x) v and s-stable s1 s2

  is-inv : (State → AnInstr × Maybe State)
         → State → BExpr → Bool
  is-inv ab s b = s-stable s (step1 ab b s s)

  mutual
    find-inv : (State → AnInstr × Maybe State) → BExpr → State → State → Instr → ℕ → State
    find-inv ab b init s i n =
      let s' = step2 ab b init s (choose-1 s i) in
      if is-inv ab s' b then s' else find-inv-aux ab b init s s' i n

    find-inv-aux : (State → AnInstr × Maybe State) → BExpr → State → State → State → Instr → ℕ → State
    find-inv-aux ab b init s s' i  zero   = []
    find-inv-aux ab b init s s' i (suc n) =
      find-inv ab b init (over-approx n s s') i n

  do-annot : (State → AnInstr × Maybe State)
           → BExpr → State → Instr → AnInstr
  do-annot ab b s i = recᵐ (mark i) (λ s′ → ab s′ .fst) (learn-from-success s b)

  ab2 : Instr → State → AnInstr × Maybe State
  ab2 (Assign x e) s = AnPre (s→a s) (AnAssign x e) , just (stupd x (a-af s e) s)
  ab2 (Seq i₁ i₂)  s = let (a_i1 , s1) = ab2 i₁ s in
                       recᵐ ((AnSeq a_i1 (mark i₂)) , nothing)
                            (λ s1′ → let (a_i2 , s2) = ab2 i₂ s1′ in
                                     (AnSeq a_i1 a_i2) , s2)
                            s1
  ab2 (While b i)  s = let inv = find-inv (ab2 i) b s s i (choose-2 s i) in
                       (AnWhile b (s→a inv) (do-annot (ab2 i) b inv i)) , (learn-from-failure inv b)

-- testing

data Interval : 𝒰 where
  Above   : ℕ → Interval
  Below   : ℕ → Interval
  Between : ℕ → ℕ → Interval
  AllN    : Interval

i-fromN : ℕ → Interval
i-fromN x = Between x x

i-add : Interval → Interval → Interval
i-add (Above x)     (Above y)     = Above (x + y)
i-add (Above x)     (Between y _) = Above (x + y)
i-add (Below x)     (Below y)     = Below (x + y)
i-add (Below x)     (Between _ z) = Below (x + z)
i-add (Between x _) (Above z)     = Above (x + z)
i-add (Between _ y) (Below z)     = Below (y + z)
i-add (Between x y) (Between z w) = Between (x + z) (y + w)
i-add _             _             = AllN

open module OEState = State.State Interval AllN
open module OEInt = StateA Interval AllN i-add i-fromN

-- TODO upstream

minᵇ : ℕ → ℕ → ℕ
minᵇ x y = if x ≤ᵇ y then x else y

maxᵇ : ℕ → ℕ → ℕ
maxᵇ x y = if x ≤ᵇ y then y else x

i-learn-from-success-aux : State → String → Interval → Interval → Maybe State
i-learn-from-success-aux s n (Below x)     (Above y)     = if x ≤ᵇ y then nothing
                                                                     else just (stupd n (Between y (pred x)) s)
i-learn-from-success-aux s n (Below x)     (Below y)     = just (if x ≤ᵇ y then stupd n (Below (pred x)) s
                                                                           else s)
i-learn-from-success-aux s n (Below x)     (Between y z) = if x ≤ᵇ y then nothing
                                                                     else just (stupd n (Between y (minᵇ (pred x) z)) s)
i-learn-from-success-aux s n (Below x)      AllN         = just (stupd n (Below (pred x)) s)
i-learn-from-success-aux s n (Between _ y) (Above z)     = if y ≤ᵇ z then nothing
                                                                     else just (stupd n (Between z (pred y)) s)
i-learn-from-success-aux s n (Between _ y) (Below z)     = just (if y ≤ᵇ z then stupd n (Below (pred y)) s
                                                                           else s)
i-learn-from-success-aux s n (Between _ y) (Between z w) = if y ≤ᵇ z then nothing
                                                                     else just (if y ≤ᵇ w then stupd n (Between z (pred y)) s
                                                                                          else s)
i-learn-from-success-aux s n (Between _ y)  AllN         = just (stupd n (Below (pred y)) s)
i-learn-from-success-aux s _ _              _            = just s

i-learn-from-success : State → BExpr → Maybe State
i-learn-from-success s (BLt (AVar n) e) = i-learn-from-success-aux s n (a-af s e) (stlup s n)
i-learn-from-success s _                = just s

i-learn-from-failure-aux : State → String → Interval → Interval → Maybe State
i-learn-from-failure-aux s n (Above x)     (Above y)     = just (if x ≤ᵇ y then s
                                                                           else stupd n (Above x) s)
i-learn-from-failure-aux s n (Above x)     (Below y)     = if x ≤ᵇ y then just (stupd n (Between x y) s)
                                                                     else nothing
i-learn-from-failure-aux s n (Above x)     (Between y z) = if z <ᵇ x then nothing
                                                                     else just (if x ≤ᵇ y then s else stupd n (Between x z) s)
i-learn-from-failure-aux s n (Above x)      AllN         = just (stupd n (Above x) s)
i-learn-from-failure-aux s n (Between x _) (Above z)     = just (if x ≤ᵇ z then s
                                                                           else stupd n (Above x) s)
i-learn-from-failure-aux s n (Between x _) (Below z)     = if x ≤ᵇ z then just (stupd n (Between x z) s)
                                                                     else nothing
i-learn-from-failure-aux s n (Between x _) (Between z w) = if w <ᵇ x then nothing
                                                                     else just (if x ≤ᵇ z then s
                                                                                          else stupd n (Between x w) s)
i-learn-from-failure-aux s n (Between x _)  AllN         = just (stupd n (Above x) s)
i-learn-from-failure-aux s _ _              _            = just s

i-learn-from-failure : State → BExpr → Maybe State
i-learn-from-failure s (BLt (AVar n) e) = i-learn-from-failure-aux s n (a-af s e) (stlup s n)
i-learn-from-failure s _                = just s

i-to-pred : Interval → AExpr → Assert
i-to-pred (Above x)     e = QPred "leq" (ANum x ∷ e ∷ [])
i-to-pred (Below x)     e = QPred "leq" (e ∷ ANum x ∷ [])
i-to-pred (Between x y) e = QConj (QPred "leq" (ANum x ∷ e ∷ []))
                                  (QPred "leq" (e ∷ ANum y ∷ []))
i-to-pred  AllN         _ = QTrue

i-join : Interval → Interval → Interval
i-join (Above x)     (Above y)     = Above (minᵇ x y)
i-join (Above x)     (Between y _) = Above (minᵇ x y)
i-join (Below x)     (Below y)     = Below (maxᵇ x y)
i-join (Below x)     (Between _ z) = Below (maxᵇ x z)
i-join (Between x _) (Above z)     = Above (minᵇ x z)
i-join (Between _ y) (Below z)     = Below (maxᵇ y z)
i-join (Between x y) (Between z w) = Between (minᵇ x z) (maxᵇ y w)
i-join _             _             = AllN

i-thinner : Interval → Interval → Bool
i-thinner (Above x)     (Above y)     = y ≤ᵇ x
i-thinner (Below x)     (Below y)     = x ≤ᵇ y
i-thinner (Between x _) (Above z)     = z ≤ᵇ x
i-thinner (Between _ y) (Below z)     = y ≤ᵇ z
i-thinner (Between x y) (Between z w) = (z ≤ᵇ x) and (y ≤ᵇ w)
i-thinner _              AllN         = true
i-thinner _              _            = false

open-interval : Interval → Interval → Interval
open-interval i@(Above x)     (Above y)     = if x ≤ᵇ y then i else AllN
open-interval i@(Below x)     (Below y)     = if y ≤ᵇ x then i else AllN
open-interval i@(Between x y) (Between z w) = if x ≤ᵇ z
                                                  then if w ≤ᵇ y then i else Above x
                                                  else if w ≤ᵇ y then Below y else AllN
open-interval    _              _            = AllN

open-intervals : State → State → State
open-intervals s s' = map (λ p → let (n , v) = p in n , open-interval v (stlup s' n)) s

i-over-approx : ℕ → State → State → State
i-over-approx  zero   s s' = []
i-over-approx (suc _) s s' = open-intervals s s'

-- TODO prop

i-choose-1 : State → Instr → ℕ
i-choose-1 _ _ = 2

i-choose-2 : State → Instr → ℕ
i-choose-2 _ _ = 3

open module IntervalInt = AInt2 Interval AllN i-add i-fromN i-to-pred i-learn-from-success i-learn-from-failure i-join i-thinner i-over-approx i-choose-1 i-choose-2

i-1 : Instr
i-1 = While (BLt (AVar "x") (ANum 10))
            (Assign "x" (APlus (AVar "x") (ANum 1)))

s-1 : State
s-1 = ("x" , i-fromN 0) ∷ []

res-1 : AnInstr × Maybe State
res-1 =   AnWhile (BLt (AVar "x") (ANum 10))
                  (QConj
                    (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                           (QPred "leq" (AVar "x" ∷ ANum 10 ∷ [])))
                    QTrue)
                  (AnPre (QConj
                           (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                  (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                           QTrue)
                         (AnAssign "x" (APlus (AVar "x") (ANum 1))))
        , just (("x" , Between 10 10) ∷ [])

test-1 : ab2 i-1 s-1 ＝ res-1
test-1 = refl

i-3 : Instr
i-3 = While (BLt (AVar "x") (ANum 10))
            (Seq (While (BLt (AVar "y") (AVar "x"))
                        (Assign "y" (APlus (AVar "y") (ANum 1))))
            (Seq (Assign "y" (ANum 0))
                 (Assign "x" (APlus (AVar "x") (ANum 1)))))

s-3 : State
s-3 = ("x" , i-fromN 0) ∷ ("y" , i-fromN 0) ∷ []

res-3 : AnInstr × Maybe State
res-3 =   AnWhile (BLt (AVar "x") (ANum 10))
                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                (QPred "leq" (AVar "y" ∷ ANum 0 ∷ [])))
                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                (QPred "leq" (AVar "x" ∷ ANum 10 ∷ [])))
                   QTrue))
                  (AnSeq (AnWhile (BLt (AVar "y") (AVar "x"))
                                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                                (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                  (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                                (QPred "leq" (AVar "y" ∷ ANum 9 ∷ [])))
                                   QTrue))
                                  (AnPre (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                                       (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                         (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                                       (QPred "leq" (AVar "y" ∷ ANum 8 ∷ [])))
                                          QTrue))
                                         (AnAssign "y" (APlus (AVar "y") (ANum 1)))))
                  (AnSeq (AnPre (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                              (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                              (QPred "leq" (AVar "y" ∷ ANum 9 ∷ [])))
                                 QTrue))
                                (AnAssign "y" (ANum 0)))
                         (AnPre (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "x" ∷ []))
                                              (QPred "leq" (AVar "x" ∷ ANum 9 ∷ [])))
                                (QConj (QConj (QPred "leq" (ANum 0 ∷ AVar "y" ∷ []))
                                              (QPred "leq" (AVar "y" ∷ ANum 0 ∷ [])))
                                 QTrue))
                                (AnAssign "x" (APlus (AVar "x") (ANum 1))))))
        , just (("y" , Between 0 0) ∷ ("x" , Between 10 10) ∷ [])

test-3 : ab2 i-3 s-3 ＝ res-3
test-3 = refl

i-m-aux : List ℕ → 𝒰
i-m-aux (x ∷ y ∷ []) = x ≤ y
i-m-aux _            = ⊥

i-m : String → List ℕ → 𝒰
i-m s l = if s =ₛ "leq" then i-m-aux l else ⊥
