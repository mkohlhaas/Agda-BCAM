{-# OPTIONS --allow-unsolved-metas #-}

open import Solutions.Monday hiding (example₂)

module Start.Tuesday where

-----------------------------------------------------------------------------------------
--                                 Preliminaries                                       --
-----------------------------------------------------------------------------------------

------------------------
-- Pi and Sigma Types --
------------------------

module Product where
  -- The open keyword opens a given module in the current namespace.
  -- By default all of the public names of the module are opened.
  -- `using` limits the imported definitions to those explicitly listed.
  open Fin
  open Vec    using (Vec; []; _∷_)
  open Simple using (¬_)

  variable
    P Q : A → Set

  -- Pi types: dependent function types.
  -- For *every* x of type A, the predicate P x holds.
  -- Think of ∀.
  Π : (A : Set) → Pred A → Set
  Π A P = (x : A) → P x

  infix 5 _,_

  -- Sigma types: dependent product types, existential types.
  -- For *this* x of type A, the predicate `P x` holds.
  -- Think of ∃.
  record Σ (A : Set) (P : Pred A) : Set where
    constructor _,_
    field
      fst : A      --  In constructive mathematics we *must* provide an A - the WITNESS. Not so on classical logic.
      snd : P fst  -- `fst` refers to a previously introduced field! (`snd` depends on `fst`.)
                   -- `snd` proofs `fst`.
  open Σ public

  -- By depending on a boolean we can use Π-types to represent product types.
  -- Notice the `where` syntax.
  -- Π-types are a generalization of sum types.
  -- Sum types are specializations of Π-types.
  Π-× : Set → Set → Set
  Π-× A B = Π Bool λ where
    true  → A
    false → B

  -- By depending on a boolean we can use Σ-types to represent sum types.
  -- Σ-types are a generalization of sum types.
  -- Sum types are specializations of Σ-types.
  Σ-⊎ : Set → Set → Set
  Σ-⊎ A B = Σ Bool λ where
    true  → A
    false → B

  -- Use Π-types to recover function types (A → B).
  -- Π-types are generalizations of function types.
  -- We remove the dependency.
  Π-→ : Set → Set → Set
  Π-→ A B = Π A λ where
    _ → B

  -- Use Σ-types to recover product types (A × B).
  -- Σ-types are generalizations of product types.
  -- We remove the dependency.
  Σ-× : Set → Set → Set
  Σ-× A B = Σ A λ where
    _ → B

  infix 5 _×_
  _×_ : Set → Set → Set
  _×_ = Σ-×

  -- The `syntax` keyword introduces a notation that can include binders.
  infix 4 Σ-syntax
  Σ-syntax : (A : Set) → (A → Set) → Set
  Σ-syntax = Σ
  -- Reads: "There exists an x ∈ A such that B holds."
  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-----------------------------------------------------------------------------------------
--                                     Proofs                                          --
-----------------------------------------------------------------------------------------

  -- find an even ℕ
  example₁ : Σ ℕ EvenData
  example₁ = {!!}

  -- 1 is not even
  one-is-not-even : ¬ EvenData 1
  one-is-not-even = {!!}

  -- not all ℕs are even
  example₂ : ¬ Π ℕ EvenData
  example₂ = {!!}

  -- Negation of a predicate is a predicate.
  ¬∘ : Pred A → Pred A
  ¬∘ P = {!!}

  -----------------------------------------
  -- These can be proven regardless of A --
  -----------------------------------------

  -- If there is not one A for which P holds then for all A's P does not hold.
  -- `f` looks like `curry`.
  ¬∃⇒∀¬ : ¬ (Σ A P) → Π A (¬∘ P)
  ¬∃⇒∀¬ = {!!}

  -- If for all A's P does not hold then there is not one A for which P holds.
  -- `f` looks like `uncurry`.
  ∀¬⇒¬∃ : Π A (¬∘ P) → ¬ Σ A P
  ∀¬⇒¬∃ = {!!}

  -- If there is an A for which P does not hold then P does not hold for all A's.
  ∃¬⇒¬∀ : Σ A (¬∘ P) → ¬ Π A P
  ∃¬⇒¬∀ = {!!}

  -- But this cannot be proven regardless of A.
  -- We need an A but there isn't one around.
  -- Works in classical, but not in constructive mathematics.
  postulate ¬∀⇒∃¬ : ¬ Π A P → Σ A (¬∘ P)

  -- Show that ≤ is antisymmetric.
  ≤-≡ : n ≤ m → m ≤ n → n ≡ m
  ≤-≡ = {!!}

  -- By using `n ≤ m` instead of `Fin m` we can mention `n` in the output.
  take : Vec A m → n ≤ m → Vec A n
  take = {!!}

  Fin-to-≤ : (i : Fin m) → to-ℕ i < m
  Fin-to-≤ = {!!}

  -- Proof combining ∑-types and equality.
  ≤-to-Fin : n < m → Fin m
  ≤-to-Fin = {!!}

  -- 1) If we can transform the witness and
  -- 2) transform the predicate as per the transformation on the witness
  -- ⇒) then we can transform a Σ-type
  map : (f : A → B) → (∀ {x} → P x → Q (f x)) → (Σ A P → Σ B Q)
  map = {!!}

  ≤-to-Fin' : n < m → Σ[ i ∈ Fin m ] to-ℕ i ≡ n
  ≤-to-Fin' = {!!}

  Fin-≤-inv : (i : Fin m) → ≤-to-Fin (Fin-to-≤ i) ≡ i
  Fin-≤-inv = {!!}

  ≤-Fin-inv : (lt : Σ[ n ∈ ℕ ] n < m)
            → (to-ℕ (≤-to-Fin (snd lt)) , Fin-to-≤ (≤-to-Fin (snd lt))) ≡ lt
  ≤-Fin-inv = {!!}
