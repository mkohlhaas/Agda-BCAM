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

module WithAbstraction where
  open Mon      using (Bool; true; false; Pred; _≡_; refl; _+_; subst; +-comm)
  open Mon.List using (List; []; _∷_)

  filter : (A → Bool) → List A → List A
  filter f [] = []
  filter f (a ∷ as) with f a
  filter f (a ∷ as) | true  = a ∷ filter f as
  filter f (a ∷ as) | false = filter f as

  filter' : (A → Bool) → List A → List A
  filter' f [] = []
  filter' f (a ∷ as) with f a
  ...                | true  = a ∷ filter' f as
  ...                | false = filter' f as

  thm : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm n m p with +-comm n m
  thm n m p | eq = {!!}

  thm' : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm' n m p with n + m | +-comm n m
  thm' n m p | .(m + n) | refl = p

  thm'' : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm'' n m p rewrite +-comm n m = p

  thm''' : {P : Pred ℕ} (n m : ℕ) → P (n + m) → P (m + n)
  thm''' {P} n m p = subst {P = P} (+-comm n m) p

ListT : Set → Set → Set
ListT X B = ⊤ ⊎ (X × B)

module List where
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  infixr 20 _∷_

  mkList : ListT A (List A) → List A
  mkList = {!!}

  foldr : (ListT A B → B) → List A → B
  foldr = {!!}

  list-id : List A → List A
  list-id = {!!}

  incr : ListT A ℕ → ℕ
  incr = {!!}

  length : List A → ℕ
  length = {!!}

  length' : List A → ℕ
  length' = {!!}

  test₁ : length' (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
  test₁ = refl

module CoList where
  record CoList (A : Set) : Set where
    coinductive
    field
      next : ListT A (CoList A)

  open CoList

  [] : CoList A
  [] = {!!}

  _∷_ : A → CoList A → CoList A
  (a ∷ as) = {!!}

  unfoldr : (S → ListT A S) → S → CoList A
  unfoldr = {!!}

  repeat : A → CoList A
  repeat = {!!}

  take : ℕ → CoList A → List.List A
  take = {!!}

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

