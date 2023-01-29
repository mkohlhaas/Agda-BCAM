{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (Level)

module Start.Monday where

-- Two dashes to comment out the rest of the line.
{-
  Opening {-
  and closing -}
  for a multi-line comment
-}

-- In Agda all the tokens are tokenised using whitespace (with the exception of parentheses and some other symbols).
-- Agda offers unicode support.
-- We can input unicode using the backslash \ and (most of the time) typing what one would type in LaTeX.
-- If in emacs, we can put the cursor over a characted and use M-x describe-char to see how that character is inputted.
-- ⊥ is written using \bot

-- AKA the empty set, bottom, falsehood, the absurd type, the empty type, the initial object.
-- ⊥ : Set means ⊥ is a Type (Set = Type, for historical reasons).
-- The data keyword creates a data type where we list all the constructors of the types.
-- ⊥ has no constructors: there is no way of making something of type ⊥.
data ⊥ : Set where

-- AKA the singleton set, top, truth, the trivial type, the unit type, the terminal object.
-- The record keyword creates a record type.
-- Records have a single constructor.
-- To create a record you must populate all of its fields.
-- ⊤ has no fields: it is trivial to make one, and contains no information.
record ⊤ : Set where
  constructor tt

-- Bool has two constructors: one bit worth of information
data Bool : Set where
  true  : Bool
  false : Bool

----------------------------
-- Simple Composite Types --
----------------------------

-- Agda offers support for mixfix notation.
-- We use the underscores to specify where the arguments go.
-- In this case the arguments are the type parameters A and B, so we can write A × B.

-- A × B models a type packing up *both* an A *and* a B.
-- A and B are type parameters, both of type Set, i.e. types.
-- A × B itself is of type Set, i.e. a type.
-- We use the single record constructor _,_ to make something of type A × B.
-- The constructor _,_ takes two parameters: the fields fst and snd, of type A and B, respectively.
-- If we have a of type A and b of type B, then (a , b) is of type A × B.

-- AKA logical and, product type.
module Simple where
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  -- Agda has a very expressive module system (more on modules later).
  -- Every record has a module automatically attached to it.
  -- Opening a record exposes its constructor and its fields.
  -- The fields are projection functions out of the record.
  -- In the case of _×_, it exposes:
  -- fst : A × B → A
  -- snd : A × B → B
  open _×_

  -- AKA logical or, sum type, disjoint union.
  -- A ⊎ B models a type packing *either* an A *or* a B.
  -- A and B are type parameters, both of type Set, i.e. types.
  -- A ⊎ B itself is of type Set, i.e. a type.
  -- A ⊎ B has two constructors: inl and inr.
  -- The constructor inl takes something of type A as an argument and returns something of type A ⊎ B.
  -- The constructor inr takes something of type B as an argument and returns something of type A ⊎ B.
  -- We can make something of type A ⊎ B either by using inl and supplying an A, or by using inr and supplying a B.
  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  ------------------------
  -- Some Simple Proofs --
  ------------------------

  -- In constructive mathematics logical implication is modelled as function types.
  -- An object of type A → B shows that assuming an object of type A, we can construct an object of type B.
  -- Below we want to show that assuming an object of type A × B, we can construct an object of type A.
  -- We want to show that this is the case regardless of what A and B actually are.
  -- We do this using a polymorphic function that is parameterised over A and B, both of type Set.
  -- We use curly braces {} to make these function parameters implicit.
  -- When we call this function we won't have to supply the arguments A and B unless we want to.
  -- When we define this function we won't have to accept A and B as arguments unless we want to.
  -- The first line below gives the type of the function get-fst.
  -- The second line gives its definition.
  get-fst : {A : Set} {B : Set} → A × B → A
  get-fst = {!!}

  -- Agda is an *interactive* proof assistant.
  -- We don't provide our proofs/programs all at once: we develop them iteratively.
  -- We write ? where we don't yet have a program to provide, and we reload the file.
  -- What we get back is a hole where we can place the cursor and have a conversation with Agda.
  -- C-c is the prefix that we use to communicate with Agda.
  -- C-c C-l     reload the file
  -- C-c C-,     shows the goal and the context
  -- C-c C-.     shows the goal, the context, and what we have so far
  -- C-c C-c     pattern matches against a given arguments
  -- C-c C-space fill in hole
  -- C-c C-r     refines the goal: it will ask Agda to insert the first constructor we need
  -- C-c C-a     try to automatically fulfill the goal
  -- key bindings: https://agda.readthedocs.io/en/v2.6.1.3/getting-started/quick-guide.html
  get-snd : ∀ {A B} → A × B → B
  get-snd = {!!}

  -- The variable keyword enables us to declare convention for notation.
  -- Unless said otherwise, whenever we refer to A, B or C and these are not bound, we will refer to objects of type Set.
  variable
    ℓ     : Level
    A B C : Set ℓ

  -- Notice how we don't have to declare A, B and C anymore.
  curry : (A → B → C) → (A × B → C)
  curry = {!!}

  uncurry : (A × B → C) → (A → B → C)
  uncurry = {!!}

  ×-comm : A × B → B × A
  ×-comm = {!!}

  ×-assoc : (A × B) × C → A × (B × C)
  ×-assoc = {!!}

  -- Pattern matching has to be exhaustive: all cases must be addressed.
  ⊎-comm : A ⊎ B → B ⊎ A
  ⊎-comm = {!!}

  ⊎-assoc : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  ⊎-assoc = {!!}

  -- If there are no cases to be addressed there is nothing for us left to do.
  -- If you believe ⊥ exist you believe anything.
  absurd : ⊥ → A
  absurd = {!!}

  -- In constructive mathematics all proofs are constructions.
  -- How do we show that an object of type A cannot possibly be constructed, while using a construction to show so?
  -- We take the cannonically impossible-to-construct object ⊥, and show that if we were to assume the existence of A, we could use it to construct ⊥.
  ¬_ : Set ℓ → Set ℓ
  ¬ A = {!!}

  -- In classical logic double negation can be eliminated: ¬ ¬ A ⇒ A.
  -- That is however not the case in constructive mathematics:
  -- The proof ¬ ¬ A is a function that takes (A → ⊥) into ⊥, and offers no witness for A.
  -- The opposite direction is however constructive:
  ⇒¬¬ : A → ¬ ¬ A
  ⇒¬¬ = {!!}

  -- Moreover, double negation can be eliminated from non-witnesses.
  ¬¬¬⇒¬ : ¬ ¬ ¬ A → ¬ A
  ¬¬¬⇒¬ = {!!}

  -- Here we have a choice of two programs to write.
  ×-⇒-⊎₁ : A × B → A ⊎ B
  ×-⇒-⊎₁ = {!!}

  ×-⇒-⊎₂ : A × B → A ⊎ B
  ×-⇒-⊎₂ = {!!}

  -- A little more involved.
  -- Show that the implication (A ⊎ B → A × B) is not always true for all As and Bs.
  -- Not for all A and B there exist an A and B such that ...
  -- ¬ ∀ {A, B} => ∃ {A, B}
  ⊎-⇏-× : ¬ (∀ {A B} → A ⊎ B → A × B)
  ⊎-⇏-× = {!!}

variable
  ℓ : Level
  A B C D : Set ℓ

--------------------------
-- Inductive Data Types --
--------------------------

data ℕ : Set where
  -- The type of unary natural numbers.
  -- The zero constructor takes no arguments; the base case.
  -- The suc constructor takes one argument: an existing natural number; the inductive case.
  -- We represent natural numbers by using ticks: ||| ≈ 3.
  -- zero: no ticks
  -- suc: one more tick
  -- suc (suc (suc zero)) ≈ ||| ≈ 3
  -- ...
  zero : ℕ
  suc  : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

-- Compiler pragmas allow us to give instructions to Agda.
-- They are introduced with an opening {-# and a closing #-}.
-- Here we the pragma BUILTIN to tell Agda to use ℕ as the builtin type for natural numbers.
-- This allows us to say 3 instead of suc (suc (suc zero)).
{-# BUILTIN NATURAL ℕ #-}
three' : ℕ
three' = 3

-- Whenever we say n or m and they haven't been bound, they refer to natural numbers.
variable
  n m l : ℕ

-- Brief interlude: we declare the fixity of certain functions.
-- By default, all definitions have precedence 20.
-- The higher the precedence, the tighter they bind.
-- Here we also declare that _+_ is left associative, i.e. 1 + 2 + 3 is parsed as (1 + 2) + 3.
infixl 20 _+_

-- Define addition of natural numbers by structural recursion.
_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

-- In functions recursion must always occur on structurally smaller values (otherwise the computation might never terminate).
-- In Agda all computations must terminate.
-- We can tell Agda to ignore non-termination with this pragma.
{-# TERMINATING #-}
non-terminating : ℕ → ℕ
non-terminating n = non-terminating n

-- However, doing so would allow us to define elements of the type ⊥.
-- This is not considered safe: running Agda with the --safe option will make type-checking fail.
{-# TERMINATING #-}
loop : ⊥
loop = loop

-- Use structural recursion to define multiplication.
_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

-- The module keyword allows us to define modules (namespaces).
module List where
  infixr 15 _∷_ _++_

  -- Lists are another example of inductive types.
  -- The type parameter A is the type of every element in the list.
  -- They are like natural numbers, but the successor case contains an A.
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  example₁ : List Bool
  example₁ = true ∷ false ∷ []  -- [true, false]

  -- List concatenation by structural recursion.
  _++_ : List A → List A → List A
  _++_ = {!!}

  test₁ : List ℕ
  test₁ = (1 ∷ 2 ∷ 3 ∷ []) ++ (4 ∷ 5 ∷ 6 ∷ [])

  -- Apply a function (A → B) to every element of a list.
  map : (A → B) → List A → List B
  map = {!!}

  -- A base case B and an inductive case A → B → B is all we need to take a List A and make a B.
  foldr : (A → B → B) → B → List A → B
  foldr = {!!}

  foldl : (A → B → A) → A → List B → A
  foldl = {!!}

---------------------
-- Dependent Types --
---------------------

-- Dependent types are types that depend on values, objects of another type.
-- Dependent types allow us to model predicates on types.
-- A predicate P on a type A is a function taking elements of A into types.
Pred : Set → Set₁
Pred A = A → Set

-- Let us define a predicate on ℕ that models the even numbers.
-- Even numbers are taken to the type ⊤, which is trivial to satisfy.
-- Odd numbers are taken to the type ⊥, which is impossible to satisfy.
Even : Pred ℕ
Even = {!!}

-- We can now use Even as a precondition on a previous arguments.
-- Here we bind the first argument of type ℕ to the name n.
-- We then use n as an argument to the type Even.
-- As we expose the constructors of n, Even will compute.
half : (n : ℕ) → Even n → ℕ
half = {!!}

test₂ : ℕ
test₂ = half 10 _

-- There is an alternative way of defining dependent types.
-- EvenData is a data type indexed by elements of the type ℕ. (Pred ℕ = ℕ → Set.)
-- That is, for every (n : ℕ), EvenData n is a type.
-- The constructor zero constructs an element of the type EvenData zero.
-- The constructor 2+_ takes an element of the type EvenData n and constructs one of type EvenData (suc (suc n)).
-- Note that there is no constructor that constructs elements of the type Evendata (suc zero).
data EvenData : Pred ℕ where
  zero : EvenData zero
  2+_  : EvenData n → EvenData (suc (suc n))

-- We can use EvenData as a precondition too.
-- The difference is that while Even n computes automatically, we have to take EvenData n apart by pattern matching.
-- It leaves a trace of *why* n is even.
half-data : (n : ℕ) → EvenData n → ℕ
half-data = {!!}

-- Function composition: (f ∘ g) composes two functions f and g.
-- The result takes the input, feeds it through g, then feeds the result through f.
infixr 20 _∘_
_∘_ : (B → C) → (A → B) → (A → C)
_∘_ = {!!}

-----------------------------------------------
-- Example of Common Uses of Dependent Types --
-----------------------------------------------

module Fin where

  -- The type Fin n has n distinct inhabitants.
  -- Fin's constructors are normally `zero` and `suc` as in ℕ.
  -- For pedagogical reasons changed to `start` and `next`.
  data Fin : ℕ → Set where
    start : Fin (suc n)
    next  : Fin n → Fin (suc n)

  -- Note: There is no constructor for `Fin zero`.
  Fin0 : Fin zero → ⊥
  Fin0 = {!!}

  -- We can erase the type level information to get a ℕ (pronounced nat) back.
  to-ℕ : Fin n → ℕ
  to-ℕ = {!!}

  -----------
  -- Fin 1 --
  -----------

  -- Fin 1 has 1 inhabitant.
  _ : Fin 1
  _ = start

  -- Error
  -- _ : Fin 1
  -- _ = next(start)

  -----------
  -- Fin 2 --
  -----------

  -- Fin 2 has 2 inhabitants.
  _ : Fin 2
  _ = start

  _ : Fin 2
  _ = next(start)

  -- Error
  -- _ : Fin 2
  -- _ = next(next(start))

  -----------
  -- Fin 3 --
  -----------

  -- Fin 3 has 3 inhabitants.
  _ : Fin 3
  _ = start

  _ : Fin 3
  _ = next(start)

  _ : Fin 3
  _ = next(next(start))

  -- Error
  -- _ : Fin 3
  -- _ = next(next(next(start)))

  -- ... and so on

module Vec where
  open Fin

  -- Vectors are like lists, but they keep track of their length.
  -- The type Vec A n is the type of lists of length n containing values of type A.
  -- Notice that while A is a parameter (remains unchanged in all constructors), n is an index.
  -- We can bind parameters to names (since they don't change) but we cannot bind indices.
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : A → Vec A n → Vec A (suc n)

  -- Now we can define concatenation, but giving more assurances about the resulting length.
  _++_ : Vec A n → Vec A m → Vec A (n + m)
  _++_ = {!!}

  map : (A → B) → Vec A n → Vec B n
  map = {!!}

  -- Given a vector and a Fin, we can use the latter as a lookup index into the former.
  -- Question: What happens if the vector is empty?
  _!_ : Vec A n → Fin n → A
  _!_ = {!!}

  -- A vector Vec A n is just the inductive form of a function Fin n → A.
  tabulate : ∀ {n} → (Fin n → A) → Vec A n
  tabulate = {!!}

  -- same as (_!_)
  untabulate : Vec A n → (Fin n → A)
  untabulate [] ()
  untabulate (x ∷ xs) start = x
  untabulate (x ∷ xs) (next i) = untabulate xs i

  -- Note: `tabulate`, `untabulate` form an isomorphism.

-- Predicates need not be unary, they can be binary, i.e. relations!
Rel : Set → Set₁
Rel A = A → A → Set

-- Question: How many proofs are there for any n ≤ m?
-- Answer: 1
data _≤_ : Rel ℕ where
  z≤n : zero  ≤ n
  s≤s : n ≤ m → suc n ≤ suc m

_<_ : Rel ℕ
n < m = suc n ≤ m

-- _≤_ is reflexive and transitive.
≤-refl : ∀ n → n ≤ n
≤-refl = {!!}

≤-trans : n ≤ m → m ≤ l → n ≤ l
≤-trans = {!!}

----------------------------
-- Propositional Equality --
----------------------------

-- Things get interesting: We can use type indices to define propositional equality.
-- For any (x y : A) the type x ≡ y is a proof showing that x and y are in fact definitionally equal.
-- It has a single constructor refl which limits the ways of making something of type x ≡ y to those where x and y are in fact the same, i.e. x ≡ x.
-- When we pattern match against something of type x ≡ y, the constructor refl will make x and y unify: Agda will internalise the equality.
infix 10 _≡_
data _≡_ (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- Definitional equality holds when the two sides compute to the same symbols
2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = {!!}

-- Left identity: +-idˡ
-- Because of the way in which we defined _+_, zero + x ≡ x holds definitionally (the first case in the definition).
+-idˡ : ∀ x → (zero + x) ≡ x
+-idˡ = {!!}

-- We show that equality respects congruence.
cong : {a₁ a₂ : A} (f : A → B) → a₁ ≡ a₂ → f a₁ ≡ f a₂
cong = {!!}

-- A binary version that will come in use later on.
cong₂ : {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C) → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ = {!!}

-- ... and so on
cong₃ : {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} (f : A → B → C → D) → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ = {!!}

-- Right identity: +-idʳ
-- However +-idʳ does not hold definitionally.
-- We need to use proof by induction.
+-idʳ : ∀ n → (n + zero) ≡ n
+-idʳ = {!!}

example₂ : ∀ n → (1 + n) + zero ≡ (1 + n)
example₂ n = +-idʳ _

-- Equality is an equivalence relation.
-- An equivalence relation is reflexive, symmetric, and transitive.

-- Propositional equality is reflexive by construction.
-- Here we show it is also symmetric and transitive.
sym : {x y : A} → x ≡ y → y ≡ x
sym = {!!}

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = {!!}

-- Leibniz equality, transport.
subst : {x y : A} {P : Pred A} → x ≡ y → P x → P y
subst = {!!}

-- Now we can start proving slightly more interesting things!
+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc = {!!}

-- Introduce underscores on the RHS.
+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero    = {!!}
+-comm x (suc y) = {!!}
  where -- allows us to introduce local definitions
  +-suc : ∀ x y → x + suc y ≡ suc (x + y)
  +-suc = {!!}

-------------------------------------------
-- Some Tooling for Equational Reasoning --
-------------------------------------------

infix  1 begin_
infixr 2 step-≡
infix  3 _∎

begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

syntax step-≡ x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl

-- Taken from the local definition above.
+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero    y = refl
+-suc (suc x) y = cong suc (+-suc x y)

-- The equational resoning style allows us to explicitly write down the goals at each stage.
-- This starts to look like what one would do on the whiteboard or with paper and pencil.
+-comm′ : ∀ x y → x + y ≡ y + x
+-comm′ = {!!}
+-comm′ x (suc y) = begin
      (x + suc y)  ≡⟨ {!!} ⟩
      suc (x + y)  ≡⟨ {!!} ⟩
      suc (y + x)  ∎
