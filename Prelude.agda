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

  id : ∀ {i} {A : Set i} → A → A
  id x = x

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
  {-# BUILTIN REWRITE _==_ #-}

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

  ap² : ∀ {i j k} {A : Set i} {B : Set k} {C : Set j} {a a' : A} {b b' : B} (f : A → B → C) → a == a' →  b == b' → (f a b) == (f a' b')
  ap² f idp idp = idp

  ap³ : ∀ {i j k l} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {a a' : A} {b b' : B} {c c' : C} (f : A → B → C → D) → a == a' →  b == b' → c == c' → (f a b c) == (f a' b' c')
  ap³ f idp idp idp = idp

  ap⁴ : ∀ {i j k l m} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {E : Set m} {a a' : A} {b b' : B} {c c' : C} {d d' : D} (f : A → B → C → D → E) → a == a' →  b == b' → c == c' → d == d' → (f a b c d) == (f a' b' c' d')
  ap⁴ f idp idp idp idp = idp


  transport : ∀ {i j} {A : Set i} {B : A → Set j} {a a' : A} (pₐ : a == a') → B a → B a'
  transport pₐ b = coe (ap _ pₐ) b

  hfiber : ∀ {i} {A B : Set i} (f : A → B) (b : B) → Set i
  hfiber {A = A} f b = Σ A (λ a → f a == b)

  PathOver : ∀ {i j} {A : Set i} (B : A → Set j) {a₀ a₁ : A} (p : a₀ == a₁) (b₉ : B a₀) (b₁ : B a₁) → Set j
  PathOver B idp b₀ b₁ = b₀ == b₁

  infix 30 PathOver
  syntax PathOver B p u v =
    u == v [ B ↓ p ]

  ×= : ∀{i j} {A : Set i} {B : Set j}  {a a' : A} {b b' : B} → a == a' → b == b' → (a , b) == (a' , b')
  ×= idp idp = idp

  Σ= : ∀ {i j} {A : Set i} {B : A → Set j}  {a a' : A} {b : B a} {b' : B a'} → (pₐ : a == a') → transport pₐ b == b' → (a , b) == (a' , b')
  Σ= idp idp = idp

  ,= : ∀ {i j} {A : Set i} {B : Set j}  {a a' : A} {b b' : B} → a == a' → b == b' → (a , b) == (a' , b')
  ,= idp idp = idp


  Σ-r : ∀ {i j k} {A : Set i} {B : A → Set j} (C : Σ A B → Set k) → A → Set (j ⊔ k)
  Σ-r {A = A} {B = B} C a = Σ (B a) (λ b → C (a , b))

  Σ-in : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k) → A → Set (j ⊔ k)
  Σ-in {A = A} {B = B} C a = Σ (B a) (λ b → C a b)

  =, : ∀ {i j} {A : Set i} {B : Set j} {a a' : A} {b b' : B} → (a , b) == (a' , b') → (a == a') × (b == b')
  =, = {!!}

  fst-is-inj : ∀ {i j} {A : Set i} {B : A → Set j} {x y : Σ A B} → x == y → fst x == fst y
  fst-is-inj idp = idp

  is-contr : ∀ {i} → Set i → Set i
  is-contr A = Σ A (λ x → ((y : A) → x == y))

  is-prop : ∀ {i} → Set i → Set i
  is-prop A = ∀ (x y : A) → is-contr (x == y)

  is-set : ∀{i} → Set i → Set i
  is-set A = ∀ (x y : A) → is-prop (x == y)

  has-all-paths : ∀ {i} → Set i → Set i
  has-all-paths A = ∀ (a b : A) → a == b

  has-all-paths-idp : ∀ {i} (A : Set i) (pathsA : has-all-paths A) (a : A) → pathsA a a == idp
  has-all-paths-idp A pathsA a = {!pathsA!}

  has-all-paths-is-prop : ∀ {i} → {A : Set i} → has-all-paths A → is-prop A
  has-all-paths-is-prop pathsA x y = pathsA x y , λ {idp → {!!}}

  is-prop-has-all-paths : ∀ {i} → {A : Set i} → is-prop A → has-all-paths A
  is-prop-has-all-paths = {!!}



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

  eqdec-is-set : ∀ {i} {A : Set i} → eqdec A → is-set A
  eqdec-is-set = {!!}

  -- Stuff about ℕ inspired from HoTT-Agda
  S= : ∀{n m} → n == m → S n == S m
  S= idp = idp

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

  n≠Sn : (n : ℕ) → (n ≠ S n)
  n≠Sn O ()
  n≠Sn (S n) n=Sn = n≠Sn n (S-is-inj _ _ n=Sn)

  Sn≠n : (n : ℕ) → (S n ≠ n)
  Sn≠n O ()
  Sn≠n (S n) Sn=n = Sn≠n n (S-is-inj _ _ Sn=n)


  eqdecℕ : eqdec ℕ
  eqdecℕ O O = inl idp
  eqdecℕ O (S b) = inr (O≠S b)
  eqdecℕ (S a) O = inr (S≠O a)
  eqdecℕ (S a) (S b) with (eqdecℕ a b)
  ...                 | inl idp = inl idp
  ...                 | inr a≠b = inr (S-≠ a≠b)

  is-setℕ : is-set ℕ
  is-setℕ = {!!}

  data _≤_ : ℕ → ℕ → Set where
    0≤ : ∀ n → O ≤ n
    S≤ : ∀ {n m} → n ≤ m → S n ≤ S m

  n≤n : ∀ (n : ℕ) → n ≤ n
  n≤n O = 0≤ O
  n≤n (S n) = S≤ (n≤n n)

  n≤Sn : ∀ (n : ℕ) → n ≤ S n
  n≤Sn O = 0≤ _
  n≤Sn (S n) = S≤ (n≤Sn _)

  Sn≰n : ∀ (n : ℕ) → ¬ (S n ≤ n)
  Sn≰n .(S _) (S≤ Sn≤n) = Sn≰n _ Sn≤n

  Sn≰0 : ∀ (n : ℕ) → ¬ (S n ≤ O)
  Sn≰0 n ()

  ≤S : ∀ (n m : ℕ) → n ≤ S m → (n ≤ m) + (n == S m)
  ≤S = {!!}

  n≤m→n≤Sm : ∀ {n m : ℕ} → n ≤ m → n ≤ S m
  n≤m→n≤Sm (0≤ n) = 0≤ (S n)
  n≤m→n≤Sm (S≤ n≤m) = S≤ (n≤m→n≤Sm n≤m)

  Sn≤m→n≤m : ∀ {n m : ℕ} → S n ≤ m → n ≤ m
  Sn≤m→n≤m (S≤ n≤m) = n≤m→n≤Sm n≤m

  dec-≤ : ∀ n m → dec (n ≤ m)
  dec-≤ O m = inl (0≤ m)
  dec-≤ (S n) O = inr λ ()
  dec-≤ (S n) (S m) with (dec-≤ n m)
  ...               | inl n≤m = inl (S≤ n≤m)
  ...               | inr n≰m = inr λ {(S≤ n≤m) → n≰m n≤m}

  -- _<_ : ℕ → ℕ → Set
  -- n < m = (n ≤ m) × (n ≠ m)

  _<_ : ℕ → ℕ → Set
  n < m = S n ≤ m

  ≤×≠→< : ∀ {n m} → n ≤ m → n ≠ m → n < m
  ≤×≠→< = {!!}

  max : ℕ → ℕ → ℕ
  max n m with dec-≤ n m
  ...     | inl _ = n
  ...     | inr _ = m


  ≤-= : ∀ {n m k} → n ≤ m → m == k → n ≤ k
  ≤-= n≤m idp = n≤m

  =-≤ : ∀ {n m k} → n == m → m ≤ k → n ≤ k
  =-≤ idp m≤k = m≤k


  ≤T : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
  ≤T = {!!}

  n≤max : ∀ n m → n ≤ max n m
  n≤max = {!!}

  m≤max : ∀ n m → m ≤ max n m
  m≤max = {!!}


  data list {i} : Set i → Set (lsuc i) where
    nil : ∀{A} → list A
    _::_ : ∀ {A} → list A → (a : A) → list A

  ::= : ∀ {i} {A : Set i} {l l' : list A} {a a' : A} → l == l' → a == a' → (l :: a) == (l' :: a')
  ::= idp idp = idp


  =:: : ∀ {i} {A : Set i} {a b : A} {l k} → (l :: a) == (k :: b) → (l == k) × (a == b)
  =:: = {!!}

  cons≠nil : ∀ {i} {A : Set i} {l : list A} {a : A} → (l :: a) ≠ nil
  cons≠nil = {!!}

  length : ∀ {i} {A : Set i} → list A → ℕ
  length nil = 0
  length (l :: _) = S (length l)

  _++_ : ∀ {i} {A : Set i} → list A → list A → list A
  l ++ nil = l
  l ++ (l' :: a) = (l ++ l') :: a

  ifdec_>_then_else_ : ∀ {i j} {A : Set i} (B : Set j) → (dec B) → A → A → A
  ifdec b > inl x then A else B = A
  ifdec b > inr x then A else B = B

  iftrue : ∀ {i j}{A : Set i} {B : Set j} → (H : dec B) → (a : A) {a' : A} → B → (ifdec B > H then a else a') == a
  iftrue (inl _) a b = idp
  iftrue (inr ¬B) a b = ⊥-elim (¬B b)

  iffalse : ∀ {i j}{A : Set i} {B : Set j} → (H : dec B) → {a : A} (a' : A) → ¬ B → (ifdec B > H then a else a') == a'
  iffalse (inl b) a' ¬B = ⊥-elim (¬B b)
  iffalse (inr ¬B) a' b = idp


  if_≡_then_else_ : ∀ {i} {A : Set i} → ℕ → ℕ → A → A → A
  if v ≡ w then A else B = ifdec (v == w) > (eqdecℕ v w) then A else B

  if= : ∀ {i} {A : Set i} {n m : ℕ} (p : n == m) (a : A) {a' : A} → (if n ≡ m then a else a') == a
  if= p a = iftrue (eqdecℕ _ _) a p

  if≠ : ∀ {i} {A : Set i} {n m : ℕ} (p : n ≠ m) {a : A} (a' : A) → (if n ≡ m then a else a') == a'
  if≠ p a' = iffalse (eqdecℕ _ _) a' p

  record is-equiv {i j} {A : Set i} {B : Set j} (f : A → B) : Set (i ⊔ j)
    where
    field
      g : B → A
      f-g : (b : B) → f (g b) == b
      g-f : (a : A) → g (f a) == a
      adj : (a : A) → ap f (g-f a) == f-g (f a)

  -- logical equivalence
  _↔_ : ∀{i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A ↔ B = (A → B) × (B → A)

  funext : ∀ {i} {A B : Set i} (f g : A → B) → (∀ x → f x == g x) → f == g
  funext = {!!}

  funext-dep : ∀ {i} {A : Set i} {B : A → Set i} (f g : ∀ a → B a) → (∀ a → f a == g a) → f == g
  funext-dep = {!!}


  _∈-list_ : ∀ {i} {A : Set i} → A → list A → Set i
  x ∈-list nil = ⊥
  x ∈-list (l :: a) = (x ∈-list l) + (x == a)

  dec-∈-list : ∀ {i} {A : Set i} → eqdec A →  ∀ (a : A) (l : list A) → dec (a ∈-list l)
  dec-∈-list eqdecA a nil = inr λ{()}
  dec-∈-list eqdecA a (l :: b) with eqdecA a b
  ...                    | inl idp = inl (inr idp)
  ...                    | inr a≠b with dec-∈-list eqdecA a l
  ...                             | inl a∈l = inl (inl a∈l)
  ...                             | inr a∉l = inr λ{(inl a∈l) → a∉l a∈l; (inr a=b) → a≠b a=b}
