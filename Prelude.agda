{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

--
-- Prelude.agda - Some base definitions
--

module Prelude where

  open import Agda.Primitive public

  record ⊤ : Set where
    constructor tt

  {-# BUILTIN UNIT ⊤ #-}

  record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  _×_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A × B = Σ A (λ a → B)


  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ


  {-# BUILTIN NATURAL ℕ #-}

  uncurry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} →
            (φ : (a : A) → (b : B a) → C) →
            Σ A B → C
  uncurry φ (a , b) = φ a b

  curry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} →
          (ψ : Σ A B → C) →
          (a : A) → (b : B a) → C
  curry ψ a b = ψ (a , b)

  infix 30 _==_

  data _==_ {i} {A : Set i} (a : A) : A → Set i where
    idp : a == a

  {-# BUILTIN EQUALITY _==_ #-}

  infixl 20 _>>_

  _>>_ : ∀ {i} {A : Set i} {a b c : A} → a == b → b == c → a == c
  idp >> idp = idp

  _^ : ∀ {i} {A : Set i} {a b : A} → a == b → b == a
  _^ idp = idp

  coe : ∀ {a} {A B : Set a} → A == B → A → B
  coe idp x = x

  coe^ : ∀ {a} {A B : Set a} (p : A == B) {a : A} {b : B} → a == (coe (p ^) b) → (coe p a) == b 
  coe^ idp q = q

  coe= : ∀ {a} {A B : Set a} (p : A == B) {a b : A} → a == b → coe p a == coe p b
  coe= p idp = idp

  ap : ∀ {i j} {A : Set i} {C : Set j} {M N : A} (f : A → C) → M == N → (f M) == (f N)
  ap f idp = idp

  hfiber : ∀ {i} {A B : Set i} (f : A → B) (b : B) → Set i
  hfiber {A = A} f b = Σ A (λ a → f a == b)

  PathOver : ∀ {i j} {A : Set i} (B : A → Set j) {a₀ a₁ : A} (p : a₀ == a₁) (b₉ : B a₀) (b₁ : B a₁) → Set j
  PathOver B idp b₀ b₁ = b₀ == b₁

  infix 30 PathOver
  syntax PathOver B p u v =
    u == v [ B ↓ p ]

  ×= :  ∀ {A B : Set}  {a a' : A} {b b' : B} → a == a' → b == b' → (a , b) == (a' , b')
  ×= idp idp = idp

  Σ-r : ∀ {i j k} {A : Set i} {B : A → Set j} (C : Σ A B → Set k) → A → Set (j ⊔ k)
  Σ-r {A = A} {B = B} C a = Σ (B a) (λ b → C (a , b))

  Σ-in : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k) → A → Set (j ⊔ k)
  Σ-in {A = A} {B = B} C a = Σ (B a) (λ b → C a b)


  is-contr : Set → Set
  is-contr A = Σ A (λ x → ((y : A) → x == y))

  is-prop : Set → Set
  is-prop A = ∀ (x y : A) → is-contr (x == y)

  is-set : Set → Set
  is-set A = ∀ (x y : A) → is-prop (x == y)

  data ⊥ {i} : Set i where

  ⊥-elim : ∀ {i j} {A : Set i} → ⊥ {j} → A
  ⊥-elim ()

  ¬_ : ∀ {i} → Set i → Set i
  ¬ A = A → ⊥ {lzero}

  _≠_ : ∀{i} {A : Set i} (a b : A) → Set i
  a ≠ b = ¬ (a == b)

  data _+_  {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
    inl : A → A + B
    inr : B → A + B

  data Bool : Set where
    true : Bool
    false : Bool

  dec : ∀ {i} → Set i → Set i
  dec A = A + (¬ A)

  eqdec : ∀ {i} → Set i → Set i
  eqdec A = ∀ (a b : A) → dec (a == b)


  -- Stuff about ℕ inspired from HoTT-Agda
  pred : ℕ → ℕ
  pred O = O
  pred (S n) = n

  S-is-inj : ∀ n m → (S n == S m) → n == m
  S-is-inj n m p = ap pred p

  S-≠ : ∀ {n m : ℕ} (p : n ≠ m) → S n ≠ S m
  S-≠ {n} {m} n≠m  p = n≠m (S-is-inj n m p)

  private
    S≠O-type : ℕ → Set
    S≠O-type O = ⊥
    S≠O-type (S n) = ⊤

  S≠O : (n : ℕ) → S n ≠ O
  S≠O n p = coe (ap S≠O-type p) tt

  O≠S : (n : ℕ) → (O ≠ S n)
  O≠S n p = S≠O n (p ^)

  eqdecℕ : eqdec ℕ
  eqdecℕ O O = inl idp
  eqdecℕ O (S b) = inr (O≠S b)
  eqdecℕ (S a) O = inr (S≠O a)
  eqdecℕ (S a) (S b) with (eqdecℕ a b)
  ...                 | inl idp = inl idp
  ...                 | inr a≠b = inr (S-≠ a≠b)

  data _≤_ : ℕ → ℕ → Set where
    0≤ : ∀ n → O ≤ n
    S≤ : ∀ {n m} → n ≤ m → S n ≤ S m

  n≤n : ∀ (n : ℕ) → n ≤ n
  n≤n O = 0≤ O
  n≤n (S n) = S≤ (n≤n n)

  Sn≰n : ∀ (n : ℕ) → ¬ (S n ≤ n)
  Sn≰n .(S _) (S≤ Sn≤n) = Sn≰n _ Sn≤n

  n≤m→n≤Sm : ∀ {n m : ℕ} → n ≤ m → n ≤ S m
  n≤m→n≤Sm (0≤ n) = 0≤ (S n)
  n≤m→n≤Sm (S≤ n≤m) = S≤ (n≤m→n≤Sm n≤m)

  Sn≤m→n≤m : ∀ {n m : ℕ} → S n ≤ m → n ≤ m
  Sn≤m→n≤m (S≤ n≤m) = n≤m→n≤Sm n≤m

  _<_ : ℕ → ℕ → Set
  n < m = (n ≤ m) × (n ≠ m)

  data list {i} : Set i → Set (lsuc i) where
    nil : ∀{A} → list A
    _::_ : ∀ {A} → list A → (a : A) → list A

  ::= : ∀ {i} {A : Set i} {l l' : list A} {a a' : A} → l == l' → a == a' → (l :: a) == (l' :: a')
  ::= idp idp = idp

  cons≠nil : ∀ {i} {A : Set i} {l : list A} {a : A} → (l :: a) ≠ nil
  cons≠nil = {!!}

  length : ∀ {i} {A : Set i} → list A → ℕ
  length nil = 0
  length (l :: _) = S (length l)

  ifdec_>_then_else_ : ∀ {i j} {A : Set i} (B : Set j) → (dec B) → A → A → A
  ifdec b > inl x then A else B = A
  ifdec b > inr x then A else B = B

  if_≡_then_else_ : ∀ {i} {A : Set i} → ℕ → ℕ → A → A → A
  if v ≡ w then A else B = ifdec (v == w) > (eqdecℕ v w) then A else B
