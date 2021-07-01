{-# OPTIONS --without-K #-}

--
-- Implementation of Sets using lists
--

open import Prelude

module Sets {i} (A : Set i) (eqdecA : eqdec A) where
  valid : list A → Set i
  valid l = ∀ x → has-all-paths (x ∈-list l)

  set = Σ (list A) (λ l → valid l)

  valid-nil : valid nil
  valid-nil _ ()

  Ø : set
  Ø = nil , valid-nil

  valid-singleton : ∀ (x : A) → valid (nil :: x)
  valid-singleton x y (inr p) (inr q) = ap inr (is-prop-has-all-paths (eqdec-is-set eqdecA y x) p q)

  singleton : ∀ A → set
  singleton x = (nil :: x) , valid-singleton x

  add-carrier : list A → A → list A
  add-carrier l a with dec-∈-list eqdecA a l
  ...             | inl _ = l
  ...             | inr _ = l :: a

  add-valid : ∀ (s : set) a → valid (add-carrier (fst s) a)
  add-valid (l , valid-l) a x b b' with dec-∈-list eqdecA a l
  ...                                     | inl x∈l = valid-l x b b'
  ...                                     | inr x∉l with eqdecA x a
  add-valid (l , valid-l) a .a (inl x∈l) b' | inr x∉l | inl idp = ⊥-elim (x∉l x∈l)
  add-valid (l , valid-l) a .a (inr _) (inl x∈l) | inr x∉l | inl idp = ⊥-elim (x∉l x∈l)
  add-valid (l , valid-l) a .a (inr p) (inr q) | inr x∉l | inl idp = ap inr (is-prop-has-all-paths (eqdec-is-set eqdecA a a) p q)
  add-valid (l , valid-l) a x (inl x∈l) (inl x∈'l) | inr x∉l | inr _ = ap inl (valid-l x x∈l x∈'l)
  add-valid (l , valid-l) a x (inl x∈l) (inr x=a) | inr x∉l | inr x≠a = ⊥-elim (x≠a x=a)
  add-valid (l , valid-l) a x (inr x=a) b' | inr x∉l | inr x≠a = ⊥-elim (x≠a x=a)


  add : ∀ (s : set) → A → set
  add s a = add-carrier (fst s) a , add-valid s a

  _∈-set_ : A → set → Set i
  a ∈-set s = a ∈-list (fst s)

  has-all-paths-∈-set : ∀ a s → has-all-paths (a ∈-set s)
  has-all-paths-∈-set a s = snd s a

  is-prop-∈-set : ∀ a s → is-prop (a ∈-set s)
  is-prop-∈-set a s = has-all-paths-is-prop (has-all-paths-∈-set a s)

  add+ : set → list A → set
  add+ s nil = s
  add+ s (l :: a) = add (add+ s l) a

  -- -- Very inefficient implementation of the union of sets
  -- _∪-set_ : set → set → set
  -- s ∪-set s' = add+ s (fst s')

  set-of-list : list A → set
  set-of-list l = add+ Ø l

  -- -- being in the list or in its set are logically equivalent
  -- -- but being in the set is a proposition
  -- -- achieves the construction of propositional truncation in a reduced way
  ∈-set-∈-list : ∀ a l → a ∈-set set-of-list l → a ∈-list l
  ∈-set-∈-list a (l :: b) a∈s with dec-∈-list eqdecA b (fst (add+ Ø l))
  ...                          | inl _ = inl (∈-set-∈-list a l a∈s)
  ...                          | inr _ with eqdecA a b
  ...                                   | inl idp = inr idp
  ∈-set-∈-list a (l :: b) (inl a∈s) | inr _ | inr _ = inl (∈-set-∈-list a l a∈s)
  ∈-set-∈-list a (l :: b) (inr idp) | inr _ | inr b≠b = inl (⊥-elim (b≠b idp))


  ∈-list-∈-set : ∀ a l → a ∈-list l → a ∈-set (set-of-list l)
  ∈-list-∈-set a (l :: b) a∈l+ with eqdecA a b
  ∈-list-∈-set a (l :: b) (inr a=b)  | inr a≠b = ⊥-elim (a≠b a=b)
  ∈-list-∈-set a (l :: b) (inl a∈l)  | inr a≠b with dec-∈-list eqdecA b (fst (add+ Ø l))
  ...                                            | inl _ = ∈-list-∈-set a l a∈l
  ...                                            | inr _ = inl (∈-list-∈-set a l a∈l)
  ∈-list-∈-set a (l :: b) a∈l+       | inl idp with dec-∈-list eqdecA b (fst (add+ Ø l))
  ...                                           | inl a∈l = a∈l
  ...                                           | inr _ = inr idp
  -- Note that these are not *really* sets : the order matters
  -- In particular the identity types are not correct

  _∪-set_ : set → set → set
  (s , _) ∪-set (s' , _) = set-of-list (s ++ s')


  _⊂_ : set → set → Set i
  A ⊂ B = ∀ x → x ∈-set A → x ∈-set B

  has-all-paths-→ : ∀ {i} (A B : Set i) → has-all-paths B → has-all-paths (A → B)
  has-all-paths-→ A B paths-B f g = funext f g (λ x → paths-B (f x) (g x))

  has-all-paths-∀ : ∀ {i} (A : Set i) (B : A → Set i) → (∀ a → has-all-paths (B a)) → has-all-paths (∀ a →  B a)
  has-all-paths-∀ A B paths-B f g = funext-dep f g λ a → paths-B a (f a) (g a)

  is-prop-→ : ∀ {i} A B →  is-prop {i} B → is-prop (A → B)
  is-prop-→ A B prop-B = has-all-paths-is-prop (has-all-paths-→ A B (is-prop-has-all-paths prop-B))

  is-prop-∀ : ∀ {i} (A : Set i) (B : A →  Set i) →  (∀ a → is-prop (B a)) → is-prop (∀ a → B a)
  is-prop-∀ A B prop-B = has-all-paths-is-prop (has-all-paths-∀ A B (λ a → is-prop-has-all-paths (prop-B a)))

  is-prop-⊂ : ∀ A B → is-prop (A ⊂ B)
  is-prop-⊂ A B = is-prop-∀ _ _ λ a → is-prop-→ _ _ (is-prop-∈-set a B)

  _≗_ : set → set → Set i
  A ≗ B = (A ⊂ B) × (B ⊂ A)

  has-all-paths-≗ : ∀ A B → has-all-paths (A ≗ B)
  has-all-paths-≗ A B (A⊂B , B⊂A) (A⊂'B , B⊂'A) = ,= (is-prop-has-all-paths (is-prop-⊂ A B) A⊂B A⊂'B) ((is-prop-has-all-paths (is-prop-⊂ B A) B⊂A B⊂'A))

  is-prop-≗ : ∀ A B → is-prop (A ≗ B)
  is-prop-≗ A B = has-all-paths-is-prop (has-all-paths-≗ A B)

  dec-∈ : ∀ A a → dec (a ∈-set A)
  dec-∈ (A , _) a with dec-∈-list eqdecA a A
  ... | inl a∈A = inl a∈A
  ... | inr a∉A = inr a∉A

  ∈++₁ : ∀ l l' (a : A) → a ∈-list l → a ∈-list (l ++ l')
  ∈++₁ l nil a x = x
  ∈++₁ l (l' :: a₁) a x = inl (∈++₁ l l' a x)

  ∈++₂ : ∀ l l' (a : A) → a ∈-list l' → a ∈-list (l ++ l')
  ∈++₂ l (l' :: a₁) a (inl a∈l') = inl (∈++₂ l l' a a∈l')
  ∈++₂ l (l' :: a₁) a (inr idp) = inr idp

  ∈++ : ∀ l l' (a : A) → a ∈-list (l ++ l') → (a ∈-list l) + (a ∈-list l')
  ∈++ l nil a x = inl x
  ∈++ l (l' :: a₁) a (inl x) with ∈++ l l' a x
  ... | inl a∈l = inl a∈l
  ... | inr a∈l' = inr (inl a∈l')
  ∈++ l (l' :: a₁) a (inr p) = inr (inr p)


  ∈-∪₁ : ∀ {A B a} → a ∈-set A → (a ∈-set (A ∪-set B))
  ∈-∪₁ {A , _} {B = nil , _} {a} a∈A = ∈-list-∈-set a (A ++ nil) a∈A
  ∈-∪₁ {A , _} {(B :: b) , _} {a} a∈A = ∈-list-∈-set a (A ++ (B :: b)) (inl (∈++₁ A B a a∈A))

  ∈-∪₂ : ∀ {A B a} → a ∈-set B  → (a ∈-set (A ∪-set B))
  ∈-∪₂ {A , _} {B = nil , _} {a} ()
  ∈-∪₂ {A , _} {(B :: b) , _} {a} (inl a∈B) = ∈-list-∈-set a (A ++ (B :: b)) (inl (∈++₂ A B a a∈B))
  ∈-∪₂ {A , _} {(B :: b) , _} {a} (inr idp) = ∈-list-∈-set a (A ++ (B :: b)) (inr idp)

  ∉-∪ : ∀ {A B a} → ¬ (a ∈-set A) → ¬ (a ∈-set B) → ¬ (a ∈-set (A ∪-set B))
  ∉-∪ {A , _} {B , _} {a} a∉A a∉B a∈A∪B with ∈++ A B a (∈-set-∈-list _ _ a∈A∪B)
  ... | inl x = a∉A x
  ... | inr x = a∉B x

  ∈-∪ : ∀ {A B a} →  a ∈-set (A ∪-set B) → (a ∈-set A) + (a ∈-set B)
  ∈-∪ {A , _} {B , _} {a} a∈A∪B with ∈++ A B a (∈-set-∈-list _ _ a∈A∪B)
  ... | inl x = inl x
  ... | inr x = inr x


  ⊂-∪ : ∀ {A B C D} → A ⊂ B → C ⊂ D → (A ∪-set C) ⊂ (B ∪-set D)
  ⊂-∪ {A} {B} {C} {D} A⊂B C⊂D a a∈A∪C with dec-∈ A a | dec-∈ C a
  ... | inl a∈A | _ = ∈-∪₁ {B} {D} {a} (A⊂B _ a∈A)
  ... | inr a∉A | inl a∈C = ∈-∪₂ {B} {D} {a} (C⊂D _ a∈C)
  ... | inr a∉A | inr a∉C = ⊥-elim (∉-∪ {A} {C} {a} a∉A a∉C a∈A∪C)

  ∪-factor : ∀ A B C → (A ∪-set (B ∪-set C)) ≗ ((A ∪-set B) ∪-set (A ∪-set C))
  fst (∪-factor A B C) x x∈A∪B∪C with ∈-∪ {A} {B ∪-set C} {x} x∈A∪B∪C
  ... | inl x∈A = ∈-∪₁ {A ∪-set B} {A ∪-set C} {x} (∈-∪₁ {A} {B} {x} x∈A)
  ... | inr x∈A∪B with ∈-∪ {B} {C} {x} x∈A∪B
  ... | inl x∈B = ∈-∪₁ {A ∪-set B} {A ∪-set C} {x} (∈-∪₂ {A} {B} {x} x∈B)
  ... | inr x∈C = ∈-∪₂ {A ∪-set B} {A ∪-set C} {x} (∈-∪₂ {A} {C} {x} x∈C)
  snd (∪-factor A B C) x x∈A∪B∪A∪C with ∈-∪ {A ∪-set B} {A ∪-set C} {x} x∈A∪B∪A∪C
  snd (∪-factor A B C) x x∈A∪B∪A∪C | inl x∈A∪B with ∈-∪ {A} {B} {x} x∈A∪B
  ... | inl x∈A = ∈-∪₁ {A} {B ∪-set C} {x} x∈A
  ... | inr x∈B = ∈-∪₂ {A} {B ∪-set C} {x} (∈-∪₁ {B} {C} {x} x∈B)
  snd (∪-factor A B C) x x∈A∪B∪A∪C | inr x∈A∪C with ∈-∪ {A} {C} {x} x∈A∪C
  ... | inl x∈A = ∈-∪₁ {A} {B ∪-set C} {x} x∈A
  ... | inr x∈C = ∈-∪₂ {A} {B ∪-set C} {x} (∈-∪₂ {B} {C} {x} x∈C)

  ≗-⊂ : ∀ {A B C} → A ≗ B → B ⊂ C → A ⊂ C
  ≗-⊂ (A⊂B , _) B⊂C _ a∈A = B⊂C _ (A⊂B _ a∈A)

  ⊂-trans : ∀ {A B C} → A ⊂ B → B ⊂ C → A ⊂ C
  ⊂-trans A⊂B B⊂C _ a∈A = B⊂C _ (A⊂B _ a∈A)


  ∈-singleton : ∀ a → a ∈-set (singleton a)
  ∈-singleton a = inr idp

  ∈-Ø : ∀ {x} → ¬ (x ∈-set Ø)
  ∈-Ø ()

  A∪B⊂A∪B∪C : ∀ A B C → (A ∪-set B) ⊂ (A ∪-set (B ∪-set C))
  A∪B⊂A∪B∪C A B C x x∈A∪B with ∈-∪ {A} {B} x∈A∪B
  ... | inl x∈A = ∈-∪₁ {A} {B ∪-set C} x∈A
  ... | inr x∈B = ∈-∪₂ {A} {B ∪-set C} (∈-∪₁ {B} {C} x∈B)
