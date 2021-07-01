{-# OPTIONS --rewriting --without-K #-}

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


  id : ∀ {i} {A : Set i} → A → A
  id x = x

  uncurry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} →
            (φ : (a : A) → (b : B a) → C) →
            Σ A B → C
  uncurry φ (a , b) = φ a b

  curry : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} →
          (ψ : Σ A B → C) →
          (a : A) → (b : B a) → C
  curry ψ a b = ψ (a , b)

  {- Equality -}

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

  ap⁵ : ∀ {i j k l m n} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {E : Set m} {F : Set n} {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} (f : A → B → C → D → E → F) → a == a' →  b == b' → c == c' → d == d' → e == e' → (f a b c d e) == (f a' b' c' d' e')
  ap⁵ f idp idp idp idp idp = idp

  ap⁶ : ∀ {i j k l m n o} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {E : Set m} {F : Set n} {G : Set o} {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F} (α : A → B → C → D → E → F → G) → a == a' →  b == b' → c == c' → d == d' → e == e' → f == f' → (α a b c d e f) == (α a' b' c' d' e' f')
  ap⁶ f idp idp idp idp idp idp = idp

  ap⁷ : ∀ {i j k l m n o p} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {E : Set m} {F : Set n} {G : Set o} {H : Set p} {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F} {g g' : G} (α : A → B → C → D → E → F → G → H) → a == a' →  b == b' → c == c' → d == d' → e == e' → f == f' → g == g' → (α a b c d e f g) == (α a' b' c' d' e' f' g')
  ap⁷ f idp idp idp idp idp idp idp = idp

  transport : ∀ {i j} {A : Set i} {B : A → Set j} {a a' : A} (pₐ : a == a') → B a → B a'
  transport pₐ b = coe (ap _ pₐ) b

  transport₂ : ∀ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k} {a a' : A} {b b' : B} (pₐ : a == a') (q : b == b') → C a b → C a' b'
  transport₂ pₐ q c = coe (ap² _ pₐ q) c

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
  =, idp = idp , idp

  fst-is-inj : ∀ {i j} {A : Set i} {B : A → Set j} {x y : Σ A B} → x == y → fst x == fst y
  fst-is-inj idp = idp

  {- False and negation -}

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

  inl= : ∀ {i j} {A : Set i} {B : Set j} {a b : A} → a == b → _==_ {i ⊔ j} {A + B} (inl a) (inl b)
  inl= idp = idp

  inr= : ∀ {i j} {A : Set i} {B : Set j} {a b : B} → a == b → _==_ {i ⊔ j} {A + B} (inr a) (inr b)
  inr= idp = idp

  {- Booleans -}
  data Bool : Set where
    true : Bool
    false : Bool

  {- Decidability -}
  dec : ∀ {i} → Set i → Set i
  dec A = A + (¬ A)

  eqdec : ∀ {i} → Set i → Set i
  eqdec A = ∀ (a b : A) → dec (a == b)


  {- Natural numbers -}
  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

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

  {- Order on ℕ -}
  data _≤_ : ℕ → ℕ → Set where
    0≤ : ∀ n → O ≤ n
    S≤ : ∀ {n m} → n ≤ m → S n ≤ S m

  n≤n : ∀ (n : ℕ) → n ≤ n
  n≤n O = 0≤ O
  n≤n (S n) = S≤ (n≤n n)

  ≤-antisymetry : ∀ {n m} → n ≤ m → m ≤ n → n == m
  ≤-antisymetry (0≤ _) (0≤ _) = idp
  ≤-antisymetry (S≤ n≤m) (S≤ m≤n) = ap S (≤-antisymetry n≤m m≤n)

  n≤Sn : ∀ (n : ℕ) → n ≤ S n
  n≤Sn O = 0≤ _
  n≤Sn (S n) = S≤ (n≤Sn _)

  S≤S : ∀ {n m} → S n ≤ S m → n ≤ m
  S≤S (S≤ n≤m) = n≤m

  Sn≰n : ∀ (n : ℕ) → ¬ (S n ≤ n)
  Sn≰n .(S _) (S≤ Sn≤n) = Sn≰n _ Sn≤n

  Sn≰n-t : ∀ {n m} → n == m → ¬ (S n ≤ m)
  Sn≰n-t idp Sn≤n = Sn≰n _ Sn≤n

  Sn≰0 : ∀ (n : ℕ) → ¬ (S n ≤ O)
  Sn≰0 n ()

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


  ≤S : ∀ (n m : ℕ) → n ≤ S m → (n ≤ m) + (n == S m)
  ≤S .0 m (0≤ .(S m)) = inl (0≤ _)
  ≤S .1 O (S≤ (0≤ .0)) = inr idp
  ≤S .(S _) (S m) (S≤ n≤Sm) with ≤S _ _ n≤Sm
  ... | inl n≤m = inl (S≤ n≤m)
  ... | inr n=Sm = inr (ap S n=Sm)

  ≤-= : ∀ {n m k} → n ≤ m → m == k → n ≤ k
  ≤-= n≤m idp = n≤m

  =-≤ : ∀ {n m k} → n == m → m ≤ k → n ≤ k
  =-≤ idp m≤k = m≤k

  =-≤-= : ∀ {n m k l} → n == m → m ≤ k → k == l → n ≤ l
  =-≤-= idp m≤k idp = m≤k

  ≤T : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
  ≤T (0≤ _) _ = 0≤ _
  ≤T (S≤ n≤m) (S≤ m≤k) = S≤ (≤T n≤m m≤k)

  {- Strict order on ℕ -}
  _<_ : ℕ → ℕ → Set
  n < m = S n ≤ m

  ≤×≠→< : ∀ {n m} → n ≤ m → n ≠ m → n < m
  ≤×≠→< {.0} {.0} (0≤ O) n≠m = ⊥-elim (n≠m idp)
  ≤×≠→< {.0} {.(S m)} (0≤ (S m)) n≠m = S≤ (0≤ _)
  ≤×≠→< (S≤ n≤m) Sn≠Sm = S≤ (≤×≠→< n≤m λ n=m → Sn≠Sm (ap S n=m))

  ≰ : ∀ {n m } → ¬ (n ≤ m) → m < n
  ≰ {O} {m} n≰m = ⊥-elim (n≰m (0≤ _))
  ≰ {S n} {O} n≰m = S≤ (0≤ _)
  ≰ {S n} {S m} n≰m = S≤ (≰ λ n≤m → n≰m (S≤ n≤m))

  ℕ-trichotomy : ∀ n m → ((n < m) + (m < n)) + (n == m)
  ℕ-trichotomy n m with dec-≤ n m
  ... | inr n≰m = inl (inr (≰ n≰m))
  ... | inl n≤m with eqdecℕ n m
  ... | inl n=m = inr n=m
  ... | inr n≠m = inl (inl (≤×≠→< n≤m n≠m))

  {- Minimum and maximum -}
  max : ℕ → ℕ → ℕ
  max n m with dec-≤ n m
  ...     | inl _ = m
  ...     | inr _ = n

  n≤max : ∀ n m → n ≤ max n m
  n≤max n m with dec-≤ n m
  ... | inl n≤m = n≤m
  ... | inr m≤n = n≤n _

  m≤max : ∀ n m → m ≤ max n m
  m≤max n m with dec-≤ n m
  ... | inl n≤m = n≤n _
  ... | inr n≰m = Sn≤m→n≤m (≰ n≰m)

  up-max : ∀ {n m k} → n ≤ k → m ≤ k → max n m ≤ k
  up-max {n} {m} {k} n≤k m≤k with dec-≤ n m
  ... | inl n≤m = m≤k
  ... | inr n≰m = n≤k

  up-maxS : ∀ {n m k} → S n ≤ k → S m ≤ k → S (max n m) ≤ k
  up-maxS {n} {m} {k} n≤k m≤k with dec-≤ n m
  ... | inl n≤m = m≤k
  ... | inr n≰m = n≤k

  simplify-max-l : ∀ {n m} → m ≤ n → max n m == n
  simplify-max-l {n} {m} m≤n with dec-≤ n m
  ... | inl n≤m = ≤-antisymetry m≤n n≤m
  ... | inr _ = idp

  simplify-max-r : ∀ {n m} → n ≤ m → max n m == m
  simplify-max-r {n} {m} n≤m with dec-≤ n m
  ... | inl _ = idp
  ... | inr n≰m = ⊥-elim (n≰m n≤m)

  min : ℕ → ℕ → ℕ
  min n m with dec-≤ n m
  ...     | inl _ = n
  ...     | inr _ = m

  -- minS : ∀ {n m} → n == m → min n (S m) == m
  -- minS = {!!}
  min≤m : ∀ n m → min n m ≤ m
  min≤m n m with dec-≤ n m
  ... | inl n≤m = n≤m
  ... | inr n≰m = n≤n _

  simplify-min-l : ∀ {n m} → n ≤ m → min n m == n
  simplify-min-l {n} {m} n≤m with dec-≤ n m
  ... | inl _ = idp
  ... | inr n≰m = ⊥-elim (n≰m n≤m)

  simplify-min-r : ∀ {n m} → m ≤ n → min n m == m
  simplify-min-r {n} {m} n≤m with dec-≤ n m
  ... | inl m≤n = ≤-antisymetry m≤n n≤m
  ... | inr _ = idp

  min<l : ∀ {n m} → min n m < n → m ≤ n
  min<l {n} {m} min<n with dec-≤ n m
  ... | inl _ = ⊥-elim (Sn≰n _ min<n)
  ... | inr _ = Sn≤m→n≤m min<n

  greater-than-min-r : ∀ {n m k} → k < n → min n m ≤ k → m ≤ k
  greater-than-min-r {n} {m} {k} k<n min≤k with dec-≤ n m
  ... | inl _ = ⊥-elim (Sn≰n _ (≤T (S≤ min≤k) k<n))
  ... | inr _ = min≤k


  {- Conditional branchings -}
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

  simplify-if : ∀ {i} {A : Set i} {n} {a b : A} → 0 < n → (if n ≡ 0 then a else b) == b
  simplify-if {n = n} {b = b} 0<n with eqdecℕ n 0
  ... | inl idp = ⊥-elim (Sn≰0 _ 0<n)
  ... | inr _ = idp


  -- logical equivalence
  _↔_ : ∀{i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A ↔ B = (A → B) × (B → A)

  {- Lists -}
  data list {i} : Set i → Set (lsuc i) where
    nil : ∀{A} → list A
    _::_ : ∀ {A} → list A → (a : A) → list A

  ::= : ∀ {i} {A : Set i} {l l' : list A} {a a' : A} → l == l' → a == a' → (l :: a) == (l' :: a')
  ::= idp idp = idp


  =:: : ∀ {i} {A : Set i} {a b : A} {l k} → (l :: a) == (k :: b) → (l == k) × (a == b)
  =:: idp = idp , idp

  cons≠nil : ∀ {i} {A : Set i} {l : list A} {a : A} → (l :: a) ≠ nil
  cons≠nil ()

  length : ∀ {i} {A : Set i} → list A → ℕ
  length nil = 0
  length (l :: _) = S (length l)

  _++_ : ∀ {i} {A : Set i} → list A → list A → list A
  l ++ nil = l
  l ++ (l' :: a) = (l ++ l') :: a

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




{- Univalence and known consequences -}

  record is-equiv {i j} {A : Set i} {B : Set j} (f : A → B) : Set (i ⊔ j)
    where
    field
      g : B → A
      f-g : (b : B) → f (g b) == b
      g-f : (a : A) → g (f a) == a
      adj : (a : A) → ap f (g-f a) == f-g (f a)

  _≃_ : ∀ {i j} → (A : Set i) (B : Set j) → Set (i ⊔ j)
  A ≃ B = Σ (A → B) λ f → is-equiv f

  postulate
    univalence : ∀ {i} {A B : Set i} → (A == B) ≃ (A ≃ B)
    funext : ∀ {i} {A B : Set i} (f g : A → B) → (∀ x → f x == g x) → f == g
    funext-dep : ∀ {i} {A : Set i} {B : A → Set i} (f g : ∀ a → B a) → (∀ a → f a == g a) → f == g

{- Definition of the first H-levels -}

  is-contr : ∀ {i} → Set i → Set i
  is-contr A = Σ A (λ x → ((y : A) → x == y))

  is-prop : ∀ {i} → Set i → Set i
  is-prop A = ∀ (x y : A) → is-contr (x == y)

  is-set : ∀{i} → Set i → Set i
  is-set A = ∀ (x y : A) → is-prop (x == y)

  has-all-paths : ∀ {i} → Set i → Set i
  has-all-paths A = ∀ (a b : A) → a == b

  {- Known properties of H-levels -}
  postulate
    has-all-paths-idp : ∀ {i} (A : Set i) (pathsA : has-all-paths A) (a : A) → pathsA a a == idp
    has-all-paths-is-prop : ∀ {i} → {A : Set i} → has-all-paths A → is-prop A
    is-prop-has-all-paths : ∀ {i} → {A : Set i} → is-prop A → has-all-paths A
    eqdec-is-set : ∀ {i} {A : Set i} → eqdec A → is-set A

  is-setℕ : is-set ℕ
  is-setℕ = eqdec-is-set eqdecℕ
