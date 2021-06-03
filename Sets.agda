{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

--
-- Implementation of Sets using lists
--

open import Prelude

module Sets {i} (A : Set i) (eqdecA : eqdec A) where

  -- TODO : move this in Prelude
  _∈-list_ : A → list A → Set i
  x ∈-list nil = ⊥
  x ∈-list (l :: a) = (x ∈-list l) + (x == a)

  dec-∈-list : ∀ a l → dec (a ∈-list l)
  dec-∈-list a nil = inr λ{()}
  dec-∈-list a (l :: b) with eqdecA a b
  ...                    | inl idp = inl (inr idp)
  ...                    | inr a≠b with dec-∈-list a l
  ...                             | inl a∈l = inl (inl a∈l)
  ...                             | inr a∉l = inr λ{(inl a∈l) → a∉l a∈l; (inr a=b) → a≠b a=b}

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
  add-carrier l a with dec-∈-list a l
  ...             | inl _ = l
  ...             | inr _ = l :: a

  add-valid : ∀ (s : set) a → valid (add-carrier (fst s) a)
  add-valid (l , valid-l) a x b b' with dec-∈-list a l
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
  _∪-set_ : set → set → set
  s ∪-set s' = add+ s (fst s')

  set-of-list : list A → set
  set-of-list l = add+ Ø l

  -- -- being in the list or in its set are logically equivalent
  -- -- but being in the set is a proposition
  -- -- achieves the construction of propositional truncation in a reduced way
  ∈-set-∈-list : ∀ a l → a ∈-set set-of-list l → a ∈-list l
  ∈-set-∈-list a (l :: b) a∈s with dec-∈-list b (fst (add+ Ø l))
  ...                          | inl _ = inl (∈-set-∈-list a l a∈s)
  ...                          | inr _ with eqdecA a b
  ...                                   | inl idp = inr idp
  ∈-set-∈-list a (l :: b) (inl a∈s) | inr _ | inr _ = inl (∈-set-∈-list a l a∈s)
  ∈-set-∈-list a (l :: b) (inr idp) | inr _ | inr b≠b = inl (⊥-elim (b≠b idp))


  ∈-list-∈-set : ∀ a l → a ∈-list l → a ∈-set (set-of-list l)
  ∈-list-∈-set a (l :: b) a∈l+ with eqdecA a b
  ∈-list-∈-set a (l :: b) (inr a=b)  | inr a≠b = ⊥-elim (a≠b a=b)
  ∈-list-∈-set a (l :: b) (inl a∈l)  | inr a≠b with dec-∈-list b (fst (add+ Ø l))
  ...                                            | inl _ = ∈-list-∈-set a l a∈l
  ...                                            | inr _ = inl (∈-list-∈-set a l a∈l)
  ∈-list-∈-set a (l :: b) a∈l+       | inl idp with dec-∈-list b (fst (add+ Ø l))
  ...                                           | inl a∈l = a∈l
  ...                                           | inr _ = inr idp

-- Not that these are not *really* sets : the order matters
-- In particular the identity types are not correct

  _⊂_ : set → set → Set i
  A ⊂ B = ∀ x → x ∈-set A → x ∈-set B


  -- Move this in the Prelude... Prove it with cubical?
  funext : ∀ {i} {A B : Set i} (f g : A → B) → (∀ x → f x == g x) → f == g
  funext = {!!}

  funext-dep : ∀ {i} {A : Set i} {B : A → Set i} (f g : ∀ a → B a) → (∀ a → f a == g a) → f == g
  funext-dep = {!!}


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
