{-# OPTIONS --allow-unsolved-metas #-}

open import Solutions.Monday
open import Solutions.Tuesday
open        Fin               using (Fin; start; next)
open        List              using (List; []; _∷_; _++_)
open        Vec               using (Vec; []; _∷_; _!_)

module Start.Wednesday where

module Isomorphism where
  open Simple  using (_⊎_; _×_; _,_; inl; inr)
  open Product using (Σ-syntax; Σ-⊎; Σ-×; Π-×; Π-→; _,_)

  infix 2 _≅_
  record _≅_ (A B : Set) : Set where
    constructor Mk≅
    field
      to      : A → B
      from    : B → A
      from∘to : ∀ a → from (to a) ≡ a
      to∘from : ∀ b → to (from b) ≡ b

  open _≅_

  Σ-⊎-≅ : Σ-⊎ A B ≅ A ⊎ B
  Σ-⊎-≅ = {!!}

  Σ-×-≅ : Σ-× A B ≅ A × B
  Σ-×-≅ = {!!}

  Π-→-≅ : Π-→ A B ≅ (A → B)
  Π-→-≅ = {!!}

  postulate
    extensionality : {P : A → Set} {f g : (a : A) → P a} → (∀ x → f x ≡ g x) → f ≡ g

  Π-×-≅ : Π-× A B ≅ A × B
  Π-×-≅ = {!!}

  curry : Π-→ A (Π-→ B C) → Π-→ (Σ-× A B) C
  curry = {!!}

  uncurry : Π-→ (Σ-× A B) C → Π-→ A (Π-→ B C)
  uncurry = {!!}

  curry-uncurry : Π-→ A (Π-→ B C) ≅ Π-→ (Σ-× A B) C
  curry-uncurry = {!!}

  Fin-≤-≅ : Fin m ≅ Σ[ n ∈ ℕ ] n < m
  Fin-≤-≅ = {!!}

  _iso-∘_ : B ≅ C → A ≅ B → A ≅ C
  _iso-∘_ = {!!}

module Dec where
  open Product using (_×_; _,_; fst; snd)
  open Simple  using (¬_)

  data Dec (A : Set) : Set where
    yes :   A → Dec A
    no  : ¬ A → Dec A

  DecEq : Set → Set
  DecEq A = (x y : A) → Dec (x ≡ y)

  elim : (A → B) → (¬ A → B) → Dec A → B
  elim = {!!}

  suc-injective : {n m : ℕ} → suc n ≡ suc m → n ≡ m
  suc-injective = {!!}

  _ℕ-≟_ : DecEq ℕ
  _ℕ-≟_ = {!!}

  next-injective : {i j : Fin n} → next i ≡ next j → i ≡ j
  next-injective = {!!}

  _Fin-≟_ : DecEq (Fin n)
  _Fin-≟_ = {!!}

  ∷-injective : {x y : A} {xs ys : List A} → _≡_ {A = List A} (x ∷ xs) (y ∷ ys) → x ≡ y × xs ≡ ys
  ∷-injective = {!!}

  infix 5 _×-dec_
  _×-dec_ : Dec A → Dec B → Dec (A × B)
  _×-dec_ = {!!}

  List-≟ : DecEq A → DecEq (List A)
  List-≟ = {!!}

record Monoid (C : Set) : Set where
  constructor MkMonoid
  field
    ε   : C
    _∙_ : C → C → C

    idˡ   : (x : C)     →  ε ∙ x      ≡ x
    idʳ   : (x : C)     →  x ∙ ε      ≡ x
    assoc : (x y z : C) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

module MonoidSolver (Symbol : Set) (symbol-≟ : Dec.DecEq Symbol) where

  infixl 20 _‵∙_
  infix  25 ‵_
  data Expr : Set where
    ‵ε   : Expr
    ‵_   : Symbol → Expr
    _‵∙_ : Expr → Expr → Expr

  infix 10 _‵≡_
  record Eqn : Set where
    constructor _‵≡_
    field
      lhs : Expr
      rhs : Expr

  NormalForm : Set
  NormalForm = List Symbol

  normalise : Expr → NormalForm
  normalise ‵ε         = []
  normalise (‵ x)      = x ∷ []
  normalise (xs ‵∙ ys) = normalise xs ++ normalise ys

  module Eval (M : Monoid C) where
    open Monoid M

    Env : Set
    Env = Symbol → C

    ⟦_⟧ : Expr → Env → C
    ⟦ ‵ε ⟧     Γ = ε
    ⟦ ‵ x ⟧    Γ = Γ x
    ⟦ x ‵∙ y ⟧ Γ = ⟦ x ⟧ Γ ∙ ⟦ y ⟧ Γ

    ⟦_⟧⇓ : NormalForm → Env → C
    ⟦ [] ⟧⇓     Γ = ε
    ⟦ x ∷ xs ⟧⇓ Γ = Γ x ∙ ⟦ xs ⟧⇓ Γ

    ++-homo : ∀ Γ (xs ys : NormalForm) → ⟦ xs ++ ys ⟧⇓ Γ ≡ ⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ
    ++-homo Γ []       ys = sym (idˡ _)
    ++-homo Γ (x ∷ xs) ys = begin
         Γ x ∙ ⟦ xs ++ ys ⟧⇓ Γ          ≡⟨ cong (_ ∙_) (++-homo Γ xs ys) ⟩
         Γ x ∙ (⟦ xs ⟧⇓ Γ ∙ ⟦ ys ⟧⇓ Γ)  ≡⟨ sym (assoc _ _ _) ⟩
         (Γ x ∙ ⟦ xs ⟧⇓ Γ) ∙ ⟦ ys ⟧⇓ Γ  ∎

    correct : ∀ Γ (expr : Expr) → ⟦ normalise expr ⟧⇓ Γ ≡ ⟦ expr ⟧ Γ
    correct Γ ‵ε         = refl
    correct Γ (‵ x)      = idʳ _
    correct Γ (le ‵∙ re) = begin
        ⟦ normalise le      ++  normalise re ⟧⇓ Γ  ≡⟨ ++-homo Γ (normalise le) (normalise re) ⟩
        ⟦ normalise le ⟧⇓ Γ ∙ ⟦ normalise re ⟧⇓ Γ  ≡⟨ cong₂ _∙_ (correct Γ le) (correct Γ re) ⟩
        ⟦ le ⟧            Γ ∙ ⟦ re ⟧            Γ  ∎

    Solution : Eqn → Set
    Solution (lhs ‵≡ rhs) =
      Dec.elim

        (λ _ → ∀ (Γ : Env) → ⟦ lhs ⟧ Γ ≡ ⟦ rhs ⟧ Γ)

        (λ _ → ⊤)
        (Dec.List-≟ symbol-≟ (normalise lhs) (normalise rhs))

    solve : (eqn : Eqn) → Solution eqn

    solve (lhs ‵≡ rhs) with Dec.List-≟ symbol-≟ (normalise lhs) (normalise rhs)
    solve (lhs ‵≡ rhs) | Dec.no  _         = tt
    solve (lhs ‵≡ rhs) | Dec.yes lhs⇓≡rhs⇓ = λ Γ → begin
        ⟦ lhs ⟧ Γ             ≡⟨ sym (correct Γ lhs) ⟩
        ⟦ normalise lhs ⟧⇓ Γ  ≡⟨ cong (λ ● → ⟦ ● ⟧⇓ Γ) lhs⇓≡rhs⇓ ⟩
        ⟦ normalise rhs ⟧⇓ Γ  ≡⟨ correct Γ rhs ⟩
        ⟦ rhs ⟧ Γ             ∎

open MonoidSolver

NAT-MONOID : Monoid ℕ
Monoid.ε     NAT-MONOID = zero
Monoid._∙_   NAT-MONOID = _+_
Monoid.idˡ   NAT-MONOID = +-idˡ
Monoid.idʳ   NAT-MONOID = +-idʳ
Monoid.assoc NAT-MONOID = +-assoc

eqn₁-auto : (x y z : ℕ) → (0 + x) + y + (y + z) ≡ x + (0 + y + 0) + (y + z + 0)
eqn₁-auto x y z =
  let
    ‵x  = start
    ‵y  = next start
    ‵z  = next (next start)
    lhs = (‵ε ‵∙ ‵ ‵x) ‵∙ ‵ ‵y ‵∙ (‵ ‵y ‵∙ ‵ ‵z)
    rhs = ‵ ‵x ‵∙ (‵ε ‵∙ ‵ ‵y ‵∙ ‵ε) ‵∙ (‵ ‵y ‵∙ ‵ ‵z ‵∙ ‵ε)
  in
  Eval.solve (Fin 3) Dec._Fin-≟_ NAT-MONOID (lhs ‵≡ rhs) λ where
    start               → x
    (next start)        → y
    (next (next start)) → z
