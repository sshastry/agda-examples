
-- statically checked sorted lists
-- see http://www2.tcs.ifi.lmu.de/~abel/DepTypes.pdf

module SortedList where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false)

----------------------------------------------------------------------
-- Curry-Howard stuff

Proposition = Set

-- intentionally blank. signifies the empty set in the type system.
data Absurd : Proposition where

-- tt = trivially true
data Truth : Proposition where
  tt : Truth

-- ∧ = conjunction
data _∧_ (A B : Proposition) : Proposition where
    _,_ : A → B → A ∧ B

fst : {A B : Proposition} → A ∧ B → A
fst (a , b) = a

snd : {A B : Proposition} → A ∧ B → B
snd (a , b) = b

-- Cartesian product = conjunction
_×_ = _∧_

-- ∨ = disjunction
data _∨_ (A B : Proposition) : Proposition where
  inl : A → A ∨ B
  inr : B → A ∨ B

-- given: A or B is true, A implies C, B implies C. then C is true.
case : {A B C : Proposition} → A ∨ B → (A → C) → (B → C) → C
case (inl a) f g = f a
case (inr b) f g = g b

-- map booleans to propositions by mapping true to Truth and false to Absurd
True : Bool → Proposition
True true = Truth
True false = Absurd

----------------------------------------------------------------------

_≤_ : ℕ → ℕ → Bool
zero ≤ n = true
suc m ≤ zero = false
suc m ≤ suc n = m ≤ n

-- proposition: ≤ is reflexive. proof: induction.
refl≤ : (n : ℕ) → True (n ≤ n)
refl≤ zero = tt
refl≤ (suc n) = refl≤ n

----------------------------------------------------------------------

data SortedList : ℕ → Set where
  ∅ : SortedList zero
  ⋉ : {n : ℕ} (m : ℕ) → True (n ≤ m) → SortedList n → SortedList m

-- the arguments to ⋉ are
-- m : a natural number to prepend to the given sorted list xs
-- p : a proof that m (the new head) is ≥ head xs
-- xs : a list such that head xs = n

-- for constant natural numbers, proofs that n ≤ m are trivial since
-- ≤ is decidable; this is why we pass in `tt` in the examples below

-- examples:
one : ℕ
one = suc zero

s1 = ⋉ one tt (⋉ zero tt ∅)
-- s2 = ⋉ zero tt (⋉ one tt ∅) -- fails statically, as desired
s3 = ⋉ one tt s1       -- normal form: ⋉ 1 tt (⋉ 1 tt (⋉ 0 tt ∅))
s4 = ⋉ (suc one) tt s1 -- normal form: ⋉ 2 tt (⋉ 1 tt (⋉ 0 tt ∅))

