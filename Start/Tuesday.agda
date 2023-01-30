{-# OPTIONS --allow-unsolved-metas #-}

open import Solutions.Monday hiding (example₂)

module Start.Tuesday where

module Product where

  open Fin
  open Vec    using (Vec; []; _∷_)
  open Simple using (¬_)

  variable
    P Q : A → Set

  Π : (A : Set) → Pred A → Set
  Π A P = (x : A) → P x

  infix 5 _,_

  record Σ (A : Set) (P : Pred A) : Set where
    constructor _,_
    field
      fst : A
      snd : P fst

  open Σ public

  Π-× : Set → Set → Set
  Π-× A B = Π Bool λ where
    true  → A
    false → B

  Σ-⊎ : Set → Set → Set
  Σ-⊎ A B = Σ Bool λ where
    true  → A
    false → B

  Π-→ : Set → Set → Set
  Π-→ A B = Π A λ where
    _ → B

  Σ-× : Set → Set → Set
  Σ-× A B = Σ A λ where
    _ → B

  infix 5 _×_
  _×_ : Set → Set → Set
  _×_ = Σ-×

  infix 4 Σ-syntax
  Σ-syntax : (A : Set) → (A → Set) → Set
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  example₁ : Σ ℕ EvenData
  example₁ = {!!}

  one-is-not-even : ¬ EvenData 1
  one-is-not-even = {!!}

  example₂ : ¬ Π ℕ EvenData
  example₂ = {!!}

  ¬∘ : Pred A → Pred A
  ¬∘ P = {!!}

  ¬∃⇒∀¬ : ¬ (Σ A P) → Π A (¬∘ P)
  ¬∃⇒∀¬ = {!!}

  ∀¬⇒¬∃ : Π A (¬∘ P) → ¬ Σ A P
  ∀¬⇒¬∃ = {!!}

  ∃¬⇒¬∀ : Σ A (¬∘ P) → ¬ Π A P
  ∃¬⇒¬∀ = {!!}

  postulate ¬∀⇒∃¬ : ¬ Π A P → Σ A (¬∘ P)

  ≤-≡ : n ≤ m → m ≤ n → n ≡ m
  ≤-≡ = {!!}

  take : Vec A m → n ≤ m → Vec A n
  take = {!!}

  Fin-to-≤ : (i : Fin m) → to-ℕ i < m
  Fin-to-≤ = {!!}

  ≤-to-Fin : n < m → Fin m
  ≤-to-Fin = {!!}

  map : (f : A → B) → (∀ {x} → P x → Q (f x)) → (Σ A P → Σ B Q)
  map = {!!}

  ≤-to-Fin' : n < m → Σ[ i ∈ Fin m ] to-ℕ i ≡ n
  ≤-to-Fin' = {!!}

  Fin-≤-inv : (i : Fin m) → ≤-to-Fin (Fin-to-≤ i) ≡ i
  Fin-≤-inv = {!!}

  ≤-Fin-inv : (lt : Σ[ n ∈ ℕ ] n < m)
            → (to-ℕ (≤-to-Fin (snd lt)) , Fin-to-≤ (≤-to-Fin (snd lt))) ≡ lt
  ≤-Fin-inv = {!!}
