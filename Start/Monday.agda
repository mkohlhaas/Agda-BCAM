{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Primitive using (Level)

module Start.Monday where

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true  : Bool
  false : Bool

module Simple where
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_

  data _⊎_ (A B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B

  get-fst : {A : Set} {B : Set} → A × B → A
  get-fst = {!!}

  get-snd : ∀ {A B} → A × B → B
  get-snd = {!!}

  variable
    ℓ     : Level
    A B C : Set ℓ

  curry : (A → B → C) → (A × B → C)
  curry = {!!}

  uncurry : (A × B → C) → (A → B → C)
  uncurry = {!!}

  ×-comm : A × B → B × A
  ×-comm = {!!}

  ×-assoc : (A × B) × C → A × (B × C)
  ×-assoc = {!!}

  ⊎-comm : A ⊎ B → B ⊎ A
  ⊎-comm = {!!}

  ⊎-assoc : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  ⊎-assoc = {!!}

  absurd : ⊥ → A
  absurd = {!!}

  ¬_ : Set ℓ → Set ℓ
  ¬ A = {!!}

  ⇒¬¬ : A → ¬ ¬ A
  ⇒¬¬ = {!!}

  ¬¬¬⇒¬ : ¬ ¬ ¬ A → ¬ A
  ¬¬¬⇒¬ = {!!}

  ×-⇒-⊎₁ : A × B → A ⊎ B
  ×-⇒-⊎₁ = {!!}

  ×-⇒-⊎₂ : A × B → A ⊎ B
  ×-⇒-⊎₂ = {!!}

  ⊎-⇏-× : ¬ (∀ {A B} → A ⊎ B → A × B)
  ⊎-⇏-× = {!!}

variable
  ℓ : Level
  A B C D : Set ℓ

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ #-}
three' : ℕ
three' = 3

variable
  n m l : ℕ

infixl 20 _+_

_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

{-# TERMINATING #-}
non-terminating : ℕ → ℕ
non-terminating n = non-terminating n

{-# TERMINATING #-}
loop : ⊥
loop = loop

_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

module List where
  infixr 15 _∷_ _++_

  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  example₁ : List Bool
  example₁ = true ∷ false ∷ []

  _++_ : List A → List A → List A
  _++_ = {!!}

  test₁ : List ℕ
  test₁ = (1 ∷ 2 ∷ 3 ∷ []) ++ (4 ∷ 5 ∷ 6 ∷ [])

  map : (A → B) → List A → List B
  map = {!!}

  foldr : (A → B → B) → B → List A → B
  foldr = {!!}

  foldl : (A → B → A) → A → List B → A
  foldl = {!!}

Pred : Set → Set₁
Pred A = A → Set

Even : Pred ℕ
Even = {!!}

half : (n : ℕ) → Even n → ℕ
half = {!!}

test₂ : ℕ
test₂ = half 10 _

data EvenData : Pred ℕ where
  zero : EvenData zero
  2+_  : EvenData n → EvenData (suc (suc n))

half-data : (n : ℕ) → EvenData n → ℕ
half-data = {!!}

infixr 20 _∘_
_∘_ : (B → C) → (A → B) → (A → C)
_∘_ = {!!}

module Fin where

  data Fin : ℕ → Set where
    start : Fin (suc n)
    next  : Fin n → Fin (suc n)

  Fin0 : Fin zero → ⊥
  Fin0 = {!!}

  to-ℕ : Fin n → ℕ
  to-ℕ = {!!}

  _ : Fin 1
  _ = start

  _ : Fin 2
  _ = start

  _ : Fin 2
  _ = next(start)

  _ : Fin 3
  _ = start

  _ : Fin 3
  _ = next(start)

  _ : Fin 3
  _ = next(next(start))

module Vec where
  open Fin

  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : A → Vec A n → Vec A (suc n)

  _++_ : Vec A n → Vec A m → Vec A (n + m)
  _++_ = {!!}

  map : (A → B) → Vec A n → Vec B n
  map = {!!}

  _!_ : Vec A n → Fin n → A
  _!_ = {!!}

  tabulate : ∀ {n} → (Fin n → A) → Vec A n
  tabulate = {!!}

  untabulate : Vec A n → (Fin n → A)
  untabulate [] ()
  untabulate (x ∷ xs) start = x
  untabulate (x ∷ xs) (next i) = untabulate xs i

Rel : Set → Set₁
Rel A = A → A → Set

data _≤_ : Rel ℕ where
  z≤n : zero  ≤ n
  s≤s : n ≤ m → suc n ≤ suc m

_<_ : Rel ℕ
n < m = suc n ≤ m

≤-refl : ∀ n → n ≤ n
≤-refl = {!!}

≤-trans : n ≤ m → m ≤ l → n ≤ l
≤-trans = {!!}

infix 10 _≡_

data _≡_ (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = {!!}

+-idˡ : ∀ x → (zero + x) ≡ x
+-idˡ = {!!}

cong : {a₁ a₂ : A} (f : A → B) → a₁ ≡ a₂ → f a₁ ≡ f a₂
cong = {!!}

cong₂ : {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C) → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ = {!!}

cong₃ : {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} (f : A → B → C → D) → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ = {!!}

+-idʳ : ∀ n → (n + zero) ≡ n
+-idʳ = {!!}

example₂ : ∀ n → (1 + n) + zero ≡ (1 + n)
example₂ n = +-idʳ _

sym : {x y : A} → x ≡ y → y ≡ x
sym = {!!}

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = {!!}

subst : {x y : A} {P : Pred A} → x ≡ y → P x → P y
subst = {!!}

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc = {!!}

+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero    = {!!}
+-comm x (suc y) = {!!}
  where
  +-suc : ∀ x y → x + suc y ≡ suc (x + y)
  +-suc = {!!}

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

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero    y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-comm′ : ∀ x y → x + y ≡ y + x
+-comm′ = {!!}
+-comm′ x (suc y) = begin
      (x + suc y)  ≡⟨ {!!} ⟩
      suc (x + y)  ≡⟨ {!!} ⟩
      suc (y + x)  ∎
