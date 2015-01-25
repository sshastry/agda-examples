
This file was typed up while watching the excellent video

Type Theory Corner - Introduction to Agda
    https://www.youtube.com/watch?v=SQama_q9qtQ

with some help from
    http://oxij.org/note/BrutalDepTypes/

compare with decTotalOrder in [Data.Nat](http://agda.github.io/agda-stdlib/Data.Nat.html)

\begin{code}
module NatTotalOrder where

open import Level -- pertains to Russel's paradox on the set of all sets

-- no constructors at all. idea: want a constant which can't actually be constructed
-- not to be confused with the empty set (?)
data ⊥ : Set where
\end{code}

* the signature of ¬ pertains to the hierarchy Set, Set1, Set2, ...
* the negation of some type A ∈ Set ℓ. "not A" := if we can construct
  a function from A to bottom then A must not have existed in the
  first place

\begin{code}
¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

notbot : ⊥ → ⊥
notbot ()

data ⊤ : Set where
  tt : ⊤

notnottrue : ¬ (¬ ⊤)
-- notnottrue p = ? -- c-c c-l
-- notnottrue p = { }0 -- c-c c-,
-- notnottrue p = { }0 -- c-c c-a => agda will fill in the missing code
notnottrue p = p tt
\end{code}

dependent pairs play the role of existential quantifiers

{a b} are level indices, ignore them for now
the curly braces means they are implicit parameters

least upper bound = \lub = ⊔

\begin{code}
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor
    _,_        -- a comma
  field
    π₁ : A     -- the 1st term
    π₂ : B π₁  -- the type of the 2nd term can depend on the 1st term

open Σ public

-- Make rewrite syntax work

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL    refl #-}

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

-- B can depend on x
-- syntax Σ A (λ x → B) = ∃[ x : A ] B
-- _×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
-- A × B = ∃[ x : A ] B

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A ⊎ B
  inr : (y : B) → A ⊎ B

-- Peano arithmetic
data ℕ : Set where
  ∅ : ℕ        -- zero
  1+ : ℕ → ℕ -- succ

one = 1+ ∅
two = 1+ one
three = 1+ two
-- c-c c-n expression: type in `three` and get the normal form of the expression

\end{code}

\begin{code}

-- a predicate: a type which depends on individual terms
data _≤ℕ_ : ℕ → ℕ → Set where
  ∅≤ : ∀ (n : ℕ) → ∅ ≤ℕ n -- zero is \leq any natural number, by *construction* since this is a constructor
  1+≤ : ∀ (n m : ℕ) → n ≤ℕ m → (1+ n) ≤ℕ (1+ m)
  -- for all n,m, if we have a proof that n ≤ m then we get a proof that 1+n ≤ 1+m


-- trichotomy property
_≤ℕdec_ : ∀ x y → (x ≤ℕ y) ⊎ (y ≤ℕ x)
-- x ≤ℕdec y = { x } -- c-c c-c => agda will deconstruct x
-- ∅ ≤ℕdec y = {  } -- c-c c-a => agda will fill in the code here
∅ ≤ℕdec y = inl (∅≤ y)
-- 1+ x ≤ℕdec y = { y }0 -- c-c c-c to deconstruct y
-- 1+ x ≤ℕdec ∅ = { }0 -- c-c c-a to have agda fill in the code here
1+ x ≤ℕdec ∅ = inr (∅≤ (1+ x))
1+ x ≤ℕdec 1+ y with x ≤ℕdec y
-- 1+ x ≤ℕdec 1+ y | p = { p }0  -- c-c c-c to deconstruct the sum type
-- 1+ x ≤ℕdec 1+ y | inl x₁ = inl (1+≤ x y x₁)
-- 1+ x ≤ℕdec 1+ y | inr y₁ = inr (1+≤ y x y₁)
-- change the names from x₁ y₁ (provided by agda) to p because they're proofs
1+ x ≤ℕdec 1+ y | inl p = inl (1+≤ x y p)
1+ x ≤ℕdec 1+ y | inr p = inr (1+≤ y x p)
\end{code}

Bool is called "2" just like ⊤ is called "1" and ⊥ is called "0",
because there are exactly two constructors

\begin{code}
data Bool : Set where
  true : Bool
  false : Bool

_≤_ : ℕ → ℕ → Bool
∅ ≤ y = true
1+ x ≤ ∅ = false
1+ x ≤ 1+ y = x ≤ y

-- trick to show that _≤_ and _≤ℕdec_ are equivalent:

-- this maps booleans to a type level truth value
∥_∥  : Bool → Set
∥ true ∥ = ⊤
∥ false ∥ = ⊥

-- the type of a proof that _≤_ and _≤ℕdec_ are equivalent:
≤⇒≤ℕ : ∀ x y → ∥ (x ≤ y) ∥ → (x ≤ℕ y)
≤⇒≤ℕ ∅ y p = ∅≤ y
≤⇒≤ℕ (1+ x) ∅ () -- rhs not required; the "eliminator for falsehood"
≤⇒≤ℕ (1+ x) (1+ y) p = 1+≤ x y (≤⇒≤ℕ x y p)

-- and the other direction:
≤ℕ⇒≤ : ∀ x y → (x ≤ℕ y) → ∥ (x ≤ y) ∥
≤ℕ⇒≤ .∅ y (∅≤ .y) = tt -- dot = "inaccessible pattern", not pattern matching on them, agda infers them
≤ℕ⇒≤ .(1+ n) .(1+ m) (1+≤ n m p) = ≤ℕ⇒≤ n m p

\end{code}

induction: P 0 ∧ P n → P (n + 1) → ∀ n . P n

upshot: we have

(1) the proof that forall x,y x and y satisfy a predicate or the flip of that predicate
    _≤ℕdec_ : ∀ x y → (x ≤ℕ y) ⊎ (y ≤ℕ x)

(2) the algorithm in a functional programming language which doesn't build up a proof
    _≤_ : ℕ → ℕ → Bool

(3) the morphisms which show these two notions are isomorphic
    ≤⇒≤ℕ : ∀ x y → ∥ (x ≤ y) ∥ → (x ≤ℕ y)
    ≤ℕ⇒≤ : ∀ x y → (x ≤ℕ y) → ∥ (x ≤ y) ∥

\begin{code}
data _≈_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : ∀ {x} → x ≈ x
  -- enough to define equality in agda because pattern matching has axiom K built into it
  -- http://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/

data ⟦_⟧ (A : Set) : Set where
  ε : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧

[_] : ∀ {A : Set} → A → ⟦ A ⟧
[ x ] = x ∷ ε

_++_ : ∀ {A : Set} → ⟦ A ⟧ → ⟦ A ⟧ → ⟦ A ⟧
-- x ++ y = ? -- c-c c-l
-- x ++ y = { x }0 -- c-c c-c to deconstruct x
ε ++ y = y
(x ∷ x₁) ++ y = x ∷ (x₁ ++ y)

\end{code}

\begin{code}

example : ⟦ ℕ ⟧
example = one ∷ (two ∷ ε)
-- c-c c-n example gives the normalization 1+ ∅ ∷ (1+ (1+ ∅) ∷ ε)

example2 : ⟦ ℕ ⟧
example2 = example ++ example
-- c-c c-n example2 => 1+ ∅ ∷ (1+ (1+ ∅) ∷ (1+ ∅ ∷ (1+ (1+ ∅) ∷ ε)))

-- a decidable total order
record TO (A : Set) : Set₁ where
  constructor
    makeTO
  field
    _≤A_ : A → A → Set
    refl≤ : ∀ x → x ≤A x -- note well the dependent type!
    anti≤ : ∀ {x y} → x ≤A y → y ≤A x → x ≈ y
    trans≤ : ∀ {x y z} → x ≤A y → y ≤A z → x ≤A z
    _≤dec_ : ∀ x y → (x ≤A y) ⊎ (y ≤A x) -- this is what makes it decidable. given x, y we know how to show x <= y or y <= x

ℕSorts : TO ℕ
-- ℕSorts = { }0 -- c-c c-r to refine
-- ℕSorts = makeTO { }1 { }2 { }3 { }4 { }5 -- try c-c c-, to see the types for the goal
ℕSorts = makeTO _≤ℕ_ refl≤ℕ anti≤ℕ trans≤ℕ _≤ℕdec_
  where refl≤ℕ : (x : ℕ) → x ≤ℕ x
        refl≤ℕ ∅ = ∅≤ ∅
        refl≤ℕ (1+ x) = 1+≤ x x (refl≤ℕ x)
        anti≤ℕ : {x y : ℕ} → x ≤ℕ y → y ≤ℕ x → x ≈ y
        anti≤ℕ (∅≤ .∅) (∅≤ .∅) = refl
        anti≤ℕ (1+≤ n m p) (1+≤ .m .n q) with anti≤ℕ p q
        anti≤ℕ (1+≤ .m m p) (1+≤ .m .m q) | refl = refl
        trans≤ℕ : {x y z : ℕ} → x ≤ℕ y → y ≤ℕ z → x ≤ℕ z
        trans≤ℕ (∅≤ .∅) (∅≤ z) = ∅≤ z
        trans≤ℕ (∅≤ .(1+ n)) (1+≤ n m q) = ∅≤ (1+ m)
        trans≤ℕ (1+≤ n m p) (1+≤ .m m₁ q) with trans≤ℕ p q
        trans≤ℕ (1+≤ n m p) (1+≤ .m m₁ q) | res = 1+≤ n m₁ res
\end{code}

This proves that the natural numbers are a decidable total order.
