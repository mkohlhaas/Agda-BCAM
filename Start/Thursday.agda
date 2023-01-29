{-# OPTIONS --allow-unsolved-metas --guardedness #-}

import Solutions.Monday    as Mon
import Solutions.Tuesday   as Tue
import Solutions.Wednesday as Wed

open Mon         using (⊤; tt; ℕ; zero; suc; _≡_; refl)
open Mon.Simple  using (_⊎_; inl; inr)
open Tue.Product using (Σ; _,_; fst; snd; _×_)

module Start.Thursday where

variable
  A B C S : Set

----------------------------------------------------------------------------------------------------
--                                   `with`, `rewrite`, `subst`                                   --
----------------------------------------------------------------------------------------------------

module WithAbstraction where
  open Mon      using (Bool; true; false; Pred; _≡_; refl; _+_; subst; +-comm)
  open Mon.List using (List; []; _∷_)

------------
-- `with` --
------------

  -- You can use "with abstraction" to pattern match on intermediary computations.
  -- These can be nested, or executed simultaneously.

  filter : (A → Bool) → List A → List A
  filter f [] = []
  filter f (a ∷ as) with f a
  filter f (a ∷ as) | true  = a ∷ filter f as
  filter f (a ∷ as) | false = filter f as

  -- alternative notation
  filter' : (A → Bool) → List A → List A
  filter' f [] = []
  filter' f (a ∷ as) with f a
  ...                | true  = a ∷ filter' f as
  ...                | false = filter' f as

  -- The goal type and the type of the arguments are generalised over the value of the scrutinee.
  thm : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm n m p with +-comm n m
  thm n m p | eq = {!!}  -- we are stuck here because we can't pattern match on `eq`

  -- The dot signifies that the argument is uniquely determined.
  -- The underscore signifies that we don't care what it actually is. Especially useful if it's a longish expression.
  thm' : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm' n m p with n + m | +-comm n m
  thm' n m p | .(m + n) | refl = p

---------------
-- `rewrite` --
---------------

  -- This is such a common formula that there is special syntax for it.
  thm'' : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm'' n m p rewrite +-comm n m = p

-------------
-- `subst` --
-------------

  -- Rewrite goes through the goal and all assumptions to find applicable replacements.
  -- We could use `subst` to be more explicit about *where* the rewrite happens.
  thm''' : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm''' {P} n m p = subst {P = P} (+-comm n m) p

  -- As a reminder:
  -- subst : {x y : A} {P : Pred A} → x ≡ y → P x → P y

----------------------------------------------------------------------------------------------------
--                                   A Little on Coinductive Types                                --
----------------------------------------------------------------------------------------------------

-- Stolen from https://github.com/pigworker/CS410-17/blob/master/lectures/Lec6Done.agda

-- In Haskell Lists can be infinite due to lazyness. But you don't know by looking at the signature
-- whether you are dealing with a finite or infinite list.

-- Inductive   data types are finite.
-- Coinductive data types are potentially infinite.

-- potentially infinite list
-- X is the type of the element of the list.
-- B is the type of the tail    of the list.
-- Left  side (⊤)     will go to Nil ([]).   (Ends the list.)
-- Right side (X × B) will go to Cons (_∷_). (Gives next list element.)
ListT : Set → Set → Set
ListT X B = ⊤ ⊎ (X × B)

module List where
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  infixr 20 _∷_

  -- List constructor using ListT.
  mkList : ListT A (List A) → List A
  mkList = {!!}

  -- alg = algebra
  foldr : (ListT A B → B) → List A → B
  foldr = {!!}

  list-id : List A → List A
  list-id = {!!}

  incr : ListT A ℕ → ℕ
  incr = {!!}

  -- use basic pattern matching
  length : List A → ℕ
  length = {!!}

  -- this time use `foldr`
  length' : List A → ℕ
  length' = {!!}

  test₁ : length' (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
  test₁ = refl

-- potentially infinite lists as a coinductive list
module CoList where
  record CoList (A : Set) : Set where
    coinductive
    field
      -- alternative representation:
      -- next : ⊤ ⊎ (A × CoList A)
      next : ListT A (CoList A)

  open CoList

  [] : CoList A
  [] = {!!}

  _∷_ : A → CoList A → CoList A
  (a ∷ as) = {!!}

  -- Could be used for a random number generator. (S = seed.)
  --
  --    Creates a new random number of type A
  --    and a new seed S from a given seed.
  --              |
  --              |      Initial seed.
  --              |           |
  --              |           | Infinite list of random numbers.
  --              |           |      |
  --        ^^^^^^^^^^^^^^^   ^   ^^^^^^^^
  unfoldr : (S → ListT A S) → S → CoList A
  unfoldr = {!!}

  repeat : A → CoList A
  repeat = {!!}

  take : ℕ → CoList A → List.List A
  take = {!!}

-- infinite list
module Stream where
  record Stream (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Stream A

  open Stream

  forever : A → Stream A
  forever = {!!}

  unfold : (S → A × S) → S → Stream A
  unfold = {!!}

-- Summary:
-- · List   = finite list
-- · ListT  = potentially infinite list
-- · CoList = potentially infinite list
-- · Stream = infinite list
