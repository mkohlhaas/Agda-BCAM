{-# OPTIONS --allow-unsolved-metas #-}

open import Solutions.Monday hiding (example₂)

module Solutions.Tuesday where

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
    P Q : Pred A

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
  example₁ = (0 , zero)

  -- 1 is not even
  one-is-not-even : ¬ EvenData 1
  one-is-not-even ()

  -- not all ℕs are even
  example₂ : ¬ Π ℕ EvenData
  example₂ f = one-is-not-even (f 1)

  -- Negation of a predicate is a predicate.
  ¬∘ : Pred A → Pred A
  ¬∘ P = ¬_ ∘ P

  -----------------------------------------
  -- These can be proven regardless of A --
  -----------------------------------------

  -- If there is not one A for which P holds then for all A's P does not hold.
  -- `f` looks like `curry`.
  ¬∃⇒∀¬ : ¬ (Σ A P) → Π A (¬∘ P)
  ¬∃⇒∀¬ f a p = f (a , p)

  -- If for all A's P does not hold then there is not one A for which P holds.
  -- `f` looks like `uncurry`.
  ∀¬⇒¬∃ : Π A (¬∘ P) → ¬ Σ A P
  ∀¬⇒¬∃ f (a , p) = f a p

  -- If there is an A for which P does not hold then P does not hold for all A's.
  ∃¬⇒¬∀ : Σ A (¬∘ P) → ¬ Π A P
  ∃¬⇒¬∀ (a , f) g = f (g a)

  -- But this cannot be proven regardless of A.
  -- We need an A but there isn't one around.
  -- Works in classical, but not in constructive mathematics.
  postulate ¬∀⇒∃¬ : ¬ Π A P → Σ A (¬∘ P)

  -- Show that ≤ is antisymmetric.
  ≤-≡ : n ≤ m → m ≤ n → n ≡ m
  ≤-≡ z≤n        z≤n      = refl
  ≤-≡ (s≤s n≤m) (s≤s m≤n) = cong suc (≤-≡ n≤m m≤n)

  -- By using `n ≤ m` instead of `Fin m` we can mention `n` in the output.
  take : Vec A m → n ≤ m → Vec A n
  take  _        z≤n      = []
  take (a ∷ as) (s≤s n≤m) = a ∷ take as n≤m

  Fin-to-≤ : (i : Fin m) → to-ℕ i < m
  Fin-to-≤  start   = s≤s z≤n
  Fin-to-≤ (next i) = s≤s (Fin-to-≤ i)

  -- Proof combining ∑-types and equality.
  ≤-to-Fin : n < m → Fin m
  ≤-to-Fin (s≤s z≤n)       = start
  ≤-to-Fin (s≤s (s≤s n<m)) = next (≤-to-Fin (s≤s n<m))

  -- 1) If we can transform the witness and
  -- 2) transform the predicate as per the transformation on the witness
  -- ⇒) then we can transform a Σ-type
  map : (f : A → B) → (∀ {x} → P x → Q (f x)) → (Σ A P → Σ B Q)
  map f g (x , y) = (f x , g y )

  ≤-to-Fin' : n < m → Σ[ i ∈ Fin m ] to-ℕ i ≡ n
  ≤-to-Fin' (s≤s z≤n)       = (start , refl)
  ≤-to-Fin' (s≤s (s≤s n<m)) = map next (cong suc) (≤-to-Fin' (s≤s n<m))

  -- Goal: Σ-syntax (Fin (suc (suc m))) (λ i → to-ℕ i ≡ suc n)
  -- Have: Σ-syntax (Fin      (suc m))  (λ i → to-ℕ i ≡ n)

  Fin-≤-inv : (i : Fin m) → ≤-to-Fin (Fin-to-≤ i) ≡ i
  Fin-≤-inv start           = refl
  Fin-≤-inv (next start)    = refl
  Fin-≤-inv (next (next i)) = cong next (Fin-≤-inv (next i))

  -- Goal: ≤-to-Fin (s≤s (Fin-to-≤ i)) ≡ next i
  -- Have: ≤-to-Fin      (Fin-to-≤ i)  ≡      i

  ≤-Fin-inv : (lt : Σ[ n ∈ ℕ ] n < m)
            → (to-ℕ (≤-to-Fin (snd lt)) , Fin-to-≤ (≤-to-Fin (snd lt))) ≡ lt
  ≤-Fin-inv (zero  , s≤s z≤n)       = refl
  ≤-Fin-inv (suc n , s≤s (s≤s n<m)) = cong (map suc s≤s) (≤-Fin-inv (_ , s≤s n<m))

  -- Goal: (suc (to-ℕ (≤-to-Fin (s≤s n<m))) , s≤s (Fin-to-≤ (≤-to-Fin (s≤s n<m)))) ≡ (suc n , s≤s (s≤s n<m))
  -- Have:      (to-ℕ (≤-to-Fin (s≤s n<m))  ,      Fin-to-≤ (≤-to-Fin (s≤s n<m)))  ≡ (    n ,     (s≤s n<m))
