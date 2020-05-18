{-# OPTIONS --rewriting --without-K #-}

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

  is-prop-∈-set : ∀ a s → has-all-paths (a ∈-set s)
  is-prop-∈-set a s = snd s a

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
