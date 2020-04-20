{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude

module Syntax where

  data list : Set → Set where
    nil : ∀{A} → list A
    _::_ : ∀ {A} → list A → (a : A) → list A

  ::= : ∀ {A} {l l' : list A} {a a' : A} → l == l' → a == a' → (l :: a) == (l' :: a')
  ::= idp idp = idp

  cons≠nil : ∀ {A}{l : list A} {a : A} → (l :: a) ≠ nil
  cons≠nil = {!!}


  ifdec_>_then_else_ : ∀ {i j} {A : Set i} (B : Set j) → (dec B) → A → A → A
  ifdec b > inl x then A else B = A
  ifdec b > inr x then A else B = B

  if_≡_then_else_ : ∀ {i} {A : Set i} → ℕ → ℕ → A → A → A
  if v ≡ w then A else B = ifdec (v == w) > (eqdecℕ v w) then A else B

  -- Pre-syntax
  data Pre-Ty : Set
  data Pre-Tm : Set

  data Pre-Ty where
    Pre-∗ : Pre-Ty
    Pre-⇒ : Pre-Ty → Pre-Tm → Pre-Tm → Pre-Ty

  data Pre-Tm where
    Pre-Var : ℕ → Pre-Tm

  Pre-Ctx : Set
  Pre-Ctx = list (ℕ × Pre-Ty)

  Pre-Sub : Set
  Pre-Sub = list (ℕ × Pre-Tm)

  -- Equality elimination for constructors
  Pre-⇒= : ∀ {A B t t' u u'} → A == B → t == t' → u == u' → Pre-⇒ A t u == Pre-⇒ B t' u'
  Pre-⇒= idp idp idp = idp

  Pre-Var= : ∀ {v w} → v == w → Pre-Var v == Pre-Var w
  Pre-Var= idp = idp


  -- Action of substitutions on types and terms on a syntactical level
  _[_]Pre-Ty : Pre-Ty → Pre-Sub → Pre-Ty
  _[_]Pre-Tm : Pre-Tm → Pre-Sub → Pre-Tm

  Pre-∗ [ σ ]Pre-Ty = Pre-∗
  Pre-⇒ A t u [ σ ]Pre-Ty = Pre-⇒ (A [ σ ]Pre-Ty) (t [ σ ]Pre-Tm) (u [ σ ]Pre-Tm)
  Pre-Var x [ nil ]Pre-Tm = Pre-Var x
  Pre-Var x [ σ :: (v , t) ]Pre-Tm = if x ≡ v then t else ((Pre-Var x) [ σ ]Pre-Tm)

  length : Pre-Ctx → ℕ
  length nil = O
  length (Γ :: _) = S (length Γ)

  _#_∈_ : ℕ → Pre-Ty → Pre-Ctx → Set
  _ # _ ∈ nil = ⊥
  x # A ∈ (Γ :: (y , B)) = (x # A ∈ Γ) + ((x == y) × (A == B))

  -- ## Well-formedness statements ≡ inference rules ##
  data _⊢C : Pre-Ctx → Set
  data _⊢T_ : Pre-Ctx → Pre-Ty → Set
  data _⊢t_#_ : Pre-Ctx → Pre-Tm → Pre-Ty → Set
  data _⊢S_>_ : Pre-Ctx → Pre-Sub → Pre-Ctx → Set

  data _⊢C where
    ec : nil ⊢C
    cc : ∀ {Γ A} → Γ ⊢C → Γ ⊢T A → (Γ :: ((length Γ) , A)) ⊢C

  data _⊢T_ where
    ob : ∀ {Γ} → Γ ⊢C → Γ ⊢T Pre-∗
    ar : ∀ {Γ A t u} → Γ ⊢t t # A → Γ ⊢t u # A → Γ ⊢T Pre-⇒ A t u

  data _⊢t_#_ where
    var : ∀ {Γ x A} → Γ ⊢C → x # A ∈ Γ → Γ ⊢t (Pre-Var x) # A

  data _⊢S_>_ where
    es : ∀ {Δ} → Δ ⊢C → Δ ⊢S nil > nil
    sc : ∀ {Δ Γ γ x A t} → Δ ⊢S γ > Γ → (Γ :: (x , A)) ⊢C → (Δ ⊢t t # (A [ γ ]Pre-Ty)) → Δ ⊢S (γ :: (x , t)) > (Γ :: (x , A))

  -- ## Properties of the type theory ##
  -- weakening admissibility
  wkT : ∀ {Γ A y B} → Γ ⊢T A → (Γ :: (y , B)) ⊢C → (Γ :: (y , B)) ⊢T A
  wkt : ∀ {Γ A t y B} → Γ ⊢t t # A → (Γ :: (y , B)) ⊢C → (Γ :: (y , B)) ⊢t t # A

  wkT (ob _) Γ,y:B⊢ = ob Γ,y:B⊢
  wkT (ar Γ⊢t:A Γ⊢u:A) Γ,y:B⊢ = ar (wkt Γ⊢t:A Γ,y:B⊢) (wkt Γ⊢u:A Γ,y:B⊢)
  wkt (var Γ⊢C x∈Γ) Γ,y:B⊢ = var Γ,y:B⊢ (inl x∈Γ)

  wkS : ∀ {Δ Γ γ y B} → Δ ⊢S γ > Γ → (Δ :: (y , B)) ⊢C → (Δ :: (y , B)) ⊢S γ > Γ
  wkS (es _) Δ,y:B⊢ = es Δ,y:B⊢
  wkS (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) Δ,y:B⊢ = sc (wkS Δ⊢γ:Γ Δ,y:B⊢) Γ,x:A⊢ (wkt Δ⊢t:A[γ] Δ,y:B⊢)


  -- Consistency : all objects appearing in derivable judgments are derivable
  Γ⊢A→Γ⊢ : ∀ {Γ A} → Γ ⊢T A → Γ ⊢C
  Γ⊢t:A→Γ⊢ : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢C

  Γ⊢A→Γ⊢ (ob Γ⊢) = Γ⊢
  Γ⊢A→Γ⊢ (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A→Γ⊢ Γ⊢t:A
  Γ⊢t:A→Γ⊢ (var Γ⊢ _) = Γ⊢

  Δ⊢γ:Γ→Γ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Γ ⊢C
  Δ⊢γ:Γ→Γ⊢ (es Δ⊢) = ec
  Δ⊢γ:Γ→Γ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Γ,x:A⊢

  Δ⊢γ:Γ→Δ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Δ ⊢C
  Δ⊢γ:Γ→Δ⊢ (es Δ⊢) = Δ⊢
  Δ⊢γ:Γ→Δ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ

  Γ,x:A⊢→Γ,x:A⊢A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢T A
  Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = wkT Γ⊢A Γ,x:A⊢

  Γ,x:A⊢→Γ,x:A⊢x:A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢t (Pre-Var x) # A
  Γ,x:A⊢→Γ,x:A⊢x:A Γ,x:A⊢ = var Γ,x:A⊢ (inr (idp , idp))

  Γ⊢t:A→Γ⊢A : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢T A
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc Γ⊢ Γ⊢A) (inl y∈Γ)) = wkT (Γ⊢t:A→Γ⊢A (var Γ⊢ y∈Γ)) Γ,x:A⊢
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc _ _) (inr (idp , idp))) = Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢


  -- ## cut-admissibility ##
  -- notational shortcut : if A = B a term of type A is also of type B
  trT : ∀ {Γ A B t} → A == B → Γ ⊢t t # A → Γ ⊢t t # B
  trT idp Γ⊢t:A = Γ⊢t:A

  -- action on weakened types and terms :
  -- if x is not in A, then A[<γ,(x,t)>] = A[γ] and similarly for terms
  n∉Γ : ∀ {Γ A n} → Γ ⊢C → (length Γ ≤ n) → ¬ (n # A ∈ Γ)
  n∉Γ (cc Γ⊢ _) l+1≤n (inl n∈Γ) = n∉Γ Γ⊢ (Sn≤m→n≤m l+1≤n) n∈Γ
  n∉Γ (cc Γ⊢ _) Sn≤n (inr (idp , idp)) = Sn≰n _ Sn≤n

  lΓ∉Γ : ∀ {Γ A} → Γ ⊢C → ¬ ((length Γ) # A ∈ Γ)
  lΓ∉Γ Γ⊢ = n∉Γ Γ⊢ (n≤n _)

  wk[]T : ∀ {Γ Δ γ x u A B} → Γ ⊢T A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (A [ (γ :: (x , u)) ]Pre-Ty) == (A [ γ ]Pre-Ty)
  wk[]t : ∀ {Γ Δ γ x u A t B} → Γ ⊢t t # A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (t [ (γ :: (x , u)) ]Pre-Tm) == (t [ γ ]Pre-Tm)

  wk[]T (ob Γ⊢) _ = idp
  wk[]T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ+:Γ+ = Pre-⇒= (wk[]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ+:Γ+)  (wk[]t Γ⊢t:A Δ⊢γ+:Γ+) (wk[]t Γ⊢u:A Δ⊢γ+:Γ+)
  wk[]t {x = x} (var {x = y} Γ⊢ y∈Γ) Δ⊢γ+:Γ+             with (eqdecℕ y x)
  ...                                                    | inr _ = idp
  wk[]t (var Γ⊢ l∈Γ) (sc Δ⊢γ:Γ (cc _ _) _) | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ l∈Γ)


  -- cut-admissibility : action of substitutions preserves derivability
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)

  []T (ob Γ⊢) Δ⊢γ:Γ = ob (Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ)
  []T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ = ar ([]t Γ⊢t:A Δ⊢γ:Γ) ([]t Γ⊢u:A Δ⊢γ:Γ)
  []t {Γ = (Γ :: _)} {t = Pre-Var x} (var Γ+⊢@(cc Γ⊢ _) (inl x∈Γ)) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ _ _) with (eqdecℕ x (length Γ))
  ...                                                                                     | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  ...                                                                                     | inr _ = trT (wk[]T (Γ⊢t:A→Γ⊢A (var Γ⊢ x∈Γ)) Δ⊢γ+:Γ+ ^) ([]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ)
  []t {Γ = (Γ :: _)} {t = Pre-Var x} (var Γ+⊢@(cc Γ⊢ Γ⊢A) (inr (idp , idp))) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ x₁ Δ⊢t:A[γ]) with (eqdecℕ x (length Γ))
  ...                                                                                     | inl idp = trT (wk[]T Γ⊢A Δ⊢γ+:Γ+ ^) Δ⊢t:A[γ]
  ...                                                                                     | inr x≠x = ⊥-elim (x≠x idp)

  -- ## categorical structure ##
  -- identity on the presyntax level
  Pre-id : ∀ (Γ : Pre-Ctx) → Pre-Sub
  Pre-id nil = nil
  Pre-id (Γ :: (x , A)) = (Pre-id Γ) :: (x , Pre-Var x)

  -- action of identity on types and terms is trivial on the syntax level
  [id]T : ∀ Γ A → (A [ Pre-id Γ ]Pre-Ty) == A
  [id]t : ∀ Γ t → (t [ Pre-id Γ ]Pre-Tm) == t

  [id]T Γ Pre-∗ = idp
  [id]T Γ (Pre-⇒ A t u) = Pre-⇒= ([id]T Γ A) ([id]t Γ t) ([id]t Γ u)
  [id]t nil (Pre-Var x) = idp
  [id]t (Γ :: (y , B)) (Pre-Var x) with (eqdecℕ x y)
  ...                              | inl x=y = Pre-Var= (x=y ^)
  ...                              | inr _ = [id]t Γ (Pre-Var x)


  -- identity is well-formed
  Γ⊢id:Γ : ∀ {Γ} → Γ ⊢C → Γ ⊢S Pre-id Γ > Γ
  Γ⊢id:Γ ec = es ec
  Γ⊢id:Γ Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = sc (wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢) Γ,x:A⊢ (var Γ,x:A⊢ (inr (idp , [id]T _ _)))

  -- composition on the pre-syntax
  _∘_ : Pre-Sub → Pre-Sub → Pre-Sub
  nil ∘ γ = nil
  (γ :: (x , t)) ∘ δ = (γ ∘ δ) :: (x , (t [ δ ]Pre-Tm))

  -- action of substitutions on types and terms respects composition
  -- this is only true for well-formed types, terms and substitutions
  [∘]T : ∀ {Γ Δ Θ A γ δ} → Γ ⊢T A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((A [ γ ]Pre-Ty) [ δ ]Pre-Ty) == (A [ γ ∘ δ ]Pre-Ty)
  [∘]t : ∀ {Γ Δ Θ A t γ δ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((t [ γ ]Pre-Tm) [ δ ]Pre-Tm) == (t [ γ ∘ δ ]Pre-Tm)

  [∘]T (ob _) _ _ = idp
  [∘]T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ Θ⊢δ:Δ = Pre-⇒= ([∘]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢t:A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢u:A Δ⊢γ:Γ Θ⊢δ:Δ)
  [∘]t (var {x = x} Γ,y:A⊢ x∈Γ+) (sc {x = y} Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ with (eqdecℕ x y )
  ...                                                                | inl idp = idp
  [∘]t (var Γ,y:A⊢ (inr (idp , idp))) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr x≠x = ⊥-elim (x≠x idp)
  [∘]t (var (cc Γ⊢ _) (inl x∈Γ)) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr _ = [∘]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ Θ⊢δ:Δ


  -- composition of well-formed substitutions is well-formed
  ∘-admissibility : ∀ {Γ Δ Θ γ δ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Θ ⊢S (γ ∘ δ) > Γ
  ∘-admissibility (es Δ⊢) Θ⊢δ:Δ = es (Δ⊢γ:Γ→Δ⊢ Θ⊢δ:Δ)
  ∘-admissibility (sc Δ⊢γ:Γ Γ,x:A⊢@(cc _ Γ⊢A) Δ⊢t:A[γ]) Θ⊢δ:Δ = sc (∘-admissibility Δ⊢γ:Γ Θ⊢δ:Δ) Γ,x:A⊢ (trT ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([]t Δ⊢t:A[γ] Θ⊢δ:Δ))

  -- composition is associative, this is true only for well-formed substitutions
  ∘-associativity : ∀ {Γ Δ Θ Ξ γ δ θ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Ξ ⊢S θ > Θ → ((γ ∘ δ) ∘ θ) == (γ ∘ (δ ∘ θ))
  ∘-associativity (es _) _ _ = idp
  ∘-associativity (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ Ξ⊢θ:Θ = ::= (∘-associativity Δ⊢γ:Γ Θ⊢δ:Δ Ξ⊢θ:Θ) (×= idp ([∘]t Δ⊢t:A[γ] Θ⊢δ:Δ Ξ⊢θ:Θ))

  -- To prove right-unitality, we need a analoguous of wk[]T and wk[]t for substitutions
  -- Composing if θ is a subst without x, acting (γ :: (x , u)) on it is same as acting just γ on it
  wk[]S : ∀ {Γ Δ γ x u B Θ θ} → Γ ⊢S θ > Θ → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (θ ∘ (γ :: (x , u))) == (θ ∘ γ)
  wk[]S (es _) _ = idp
  wk[]S (sc Γ⊢θ:Θ _ Γ⊢t:A[θ]) Δ⊢γ+:Γ+ = ::= (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+) (×= idp (wk[]t Γ⊢t:A[θ] Δ⊢γ+:Γ+))

  ∘-left-unit : ∀{Γ Δ γ} → Δ ⊢S γ > Γ → (Pre-id Γ ∘ γ) == γ
  ∘-left-unit (es _) = idp
  ∘-left-unit Δ⊢γ+:Γ+@(sc {x = x} Δ⊢γ:Γ (cc Γ⊢ _) _) with (eqdecℕ x x)
  ...                                                  | inl idp = ::= (wk[]S (Γ⊢id:Γ Γ⊢) Δ⊢γ+:Γ+ >> ∘-left-unit Δ⊢γ:Γ) idp
  ...                                                  | inr x≠x = ⊥-elim (x≠x idp)

  -- for some reason right unitality is valid on the presyntax, without well-formedness hypothesis
  ∘-right-unit : ∀ {Δ γ} →  (γ ∘ Pre-id Δ) == γ
  ∘-right-unit {Δ} {nil} = idp
  ∘-right-unit {Δ} {γ :: (y , t)} = ::= ∘-right-unit (×= idp ([id]t Δ t))

  -- ## Structure of CwF
  Pre-π : ∀ (Γ : Pre-Ctx) (x : ℕ) (A : Pre-Ty) → Pre-Sub
  Pre-π Γ x A = Pre-id Γ

  Γ,x:A⊢π:Γ : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢S Pre-π Γ x A > Γ
  Γ,x:A⊢π:Γ Γ,x:A⊢@(cc Γ⊢ _) = wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢

  -- ## decidability of type checking
  dec-⊢C : ∀ Γ → dec (Γ ⊢C)
  dec-⊢T : ∀ Γ A → dec (Γ ⊢T A)
  dec-⊢t : ∀ Γ A t → dec (Γ ⊢t t # A)
  dec-⊢S : ∀ Δ Γ γ → dec (Δ ⊢S γ > Γ)

  private
    Γ+⊢→Γ⊢ : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → Γ ⊢C
    Γ+⊢→Γ⊢ (cc Γ⊢ _) = Γ⊢


    Γ+⊢→x=l : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → x == length Γ
    Γ+⊢→x=l (cc _ _) = idp

    Γ+⊢→Γ⊢A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → Γ ⊢T A
    Γ+⊢→Γ⊢A (cc _ Γ⊢A) = Γ⊢A

    Γ⊢t⇒u→Γ⊢A : ∀ {Γ A t u} → Γ ⊢T Pre-⇒ A t u → Γ ⊢T A
    Γ⊢t⇒u→Γ⊢A (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A→Γ⊢A Γ⊢t:A


    Γ⊢t⇒u→Γ⊢t : ∀ {Γ A t u} → Γ ⊢T Pre-⇒ A t u → Γ ⊢t t # A
    Γ⊢t⇒u→Γ⊢t (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A

    Γ⊢t⇒u→Γ⊢u : ∀ {Γ A t u} → Γ ⊢T Pre-⇒ A t u → Γ ⊢t u # A
    Γ⊢t⇒u→Γ⊢u (ar Γ⊢t:A Γ⊢u:A) = Γ⊢u:A

    Γ⊢x:A→x∈Γ : ∀ {Γ x A} → Γ ⊢t Pre-Var x # A → x # A ∈ Γ
    Γ⊢x:A→x∈Γ (var _ x∈Γ) = x∈Γ

    Δ⊢<>:Γ→Γ=nil : ∀ {Δ Γ} → Δ ⊢S nil > Γ → Γ == nil
    Δ⊢<>:Γ→Γ=nil (es _) = idp

    Δ⊢γ:⊘→γ=nil : ∀ {Δ γ} → Δ ⊢S γ > nil → γ == nil
    Δ⊢γ:⊘→γ=nil (es _) = idp

    Δ⊢γ+:Γ+→x=y : ∀ {Δ Γ x A γ y t} → Δ ⊢S (γ :: (y , t)) > (Γ :: (x , A)) → x == y
    Δ⊢γ+:Γ+→x=y (sc _ _ _) = idp

    Δ⊢γ+:Γ+→Δ⊢t : ∀ {Δ Γ x A γ y t} → Δ ⊢S (γ :: (y , t)) > (Γ :: (x , A)) → Δ ⊢t t # (A [ γ ]Pre-Ty)
    Δ⊢γ+:Γ+→Δ⊢t (sc _ _ Δ⊢t) = Δ⊢t

    Δ⊢γ+:Γ+→Δ⊢γ : ∀ {Δ Γ x A γ y t} → Δ ⊢S (γ :: (y , t)) > (Γ :: (x , A)) → Δ ⊢S γ > Γ
    Δ⊢γ+:Γ+→Δ⊢γ (sc Δ⊢γ:Γ _ _) = Δ⊢γ:Γ



  eqdec-Ty : eqdec Pre-Ty
  eqdec-Tm : eqdec Pre-Tm

  eqdec-Ty Pre-∗ Pre-∗ = inl idp
  eqdec-Ty Pre-∗ (Pre-⇒ _ _ _) = {!!}
  eqdec-Ty (Pre-⇒ _ _ _) Pre-∗ = {!!}
  eqdec-Ty (Pre-⇒ A t u) (Pre-⇒ B t' u') with eqdec-Ty A B | eqdec-Tm t t' | eqdec-Tm u u'
  ...                                      | inl idp       | inl idp       | inl idp      = inl idp
  ...                                      | inl idp       | inl idp       | inr u≠u'     = inr {!!}
  ...                                      | inl idp       | inr _         | _            = inr {!!}
  ...                                      | inr _         | _             | _            = inr {!!}
  eqdec-Tm (Pre-Var x) (Pre-Var y) = {!!}


  dec-∈ : ∀ (Γ x A) → dec (x # A ∈ Γ)
  dec-∈ nil x A = inr λ x → x
  dec-∈ (Γ :: (y , B)) x A with (eqdecℕ y x) | (eqdec-Ty B A)
  ...                       | inl idp         | inl idp = inl (inr (idp , idp))
  ...                       | inl idp         | inr B≠A       with dec-∈ Γ x A
  ...                                                         | inl x∈Γ = inl (inl x∈Γ)
  ...                                                         | inr x∉Γ = inr λ {(inl x∈Γ) → x∉Γ x∈Γ ; (inr (_ , A=B)) → B≠A (A=B ^)}
  dec-∈ (Γ :: (y , B)) x A | inr y≠x         | _   with dec-∈ Γ x A
  ...                                               | inl x∈Γ = inl (inl x∈Γ)
  ...                                               | inr x∉Γ = inr λ{ (inl x∈Γ) → x∉Γ x∈Γ ; (inr (x=y , _)) → y≠x (x=y ^)}

  dec-⊢C nil = inl ec
  dec-⊢C (Γ :: (x , A)) with dec-⊢C Γ | eqdecℕ x (length Γ) | dec-⊢T Γ A
  ...                        | inl Γ⊢ | inl idp              | inl Γ⊢A      = inl (cc Γ⊢ Γ⊢A)
  ...                        | inl  _ | inl idp              | inr Γ⊬A      = inr λ Γ+⊢ → Γ⊬A (Γ+⊢→Γ⊢A Γ+⊢)
  ...                        | inl Γ⊢ | inr n≠l              | _            = inr λ Γ+⊢ → n≠l (Γ+⊢→x=l Γ+⊢)
  ...                        | inr Γ⊬ | _                    | _            = inr λ Γ+⊢ → Γ⊬ (Γ+⊢→Γ⊢ Γ+⊢)
  dec-⊢T Γ Pre-∗ with dec-⊢C Γ
  ...             | inl Γ⊢ = inl (ob Γ⊢)
  ...             | inr Γ⊬ = inr λ Γ⊢* → Γ⊬ (Γ⊢A→Γ⊢ Γ⊢*)
  dec-⊢T Γ (Pre-⇒ A t u) with dec-⊢t Γ A t | dec-⊢t Γ A u
  ...                     | inl Γ⊢t:A    | inl Γ⊢u:A = inl (ar Γ⊢t:A Γ⊢u:A)
  ...                     | inl _        | inr Γ⊬u:A = inr λ Γ⊢t⇒u → Γ⊬u:A (Γ⊢t⇒u→Γ⊢u Γ⊢t⇒u)
  ...                     | inr Γ⊬t:A    | _         = inr λ Γ⊢t⇒u → Γ⊬t:A (Γ⊢t⇒u→Γ⊢t Γ⊢t⇒u)

  dec-⊢t Γ A (Pre-Var x) with dec-⊢C Γ       | dec-∈ Γ x A
  ...                     | inl Γ⊢          | inl x∈Γ      = inl (var Γ⊢ x∈Γ)
  ...                     | inl _           | inr x∉Γ      = inr λ Γ⊢x:A → x∉Γ (Γ⊢x:A→x∈Γ Γ⊢x:A)
  ...                     | inr Γ⊬          | _            = inr λ Γ⊢x:A → Γ⊬ (Γ⊢t:A→Γ⊢ Γ⊢x:A)
  dec-⊢S Δ nil nil with dec-⊢C Δ
  ...              | inl Δ⊢ = inl (es Δ⊢)
  ...              | inr Δ⊬ = inr λ Δ⊢<>:⊘ → Δ⊬ (Δ⊢γ:Γ→Δ⊢ Δ⊢<>:⊘)
  dec-⊢S Δ (Γ :: _) nil = inr λ Δ⊢<>:Γ → cons≠nil (Δ⊢<>:Γ→Γ=nil Δ⊢<>:Γ)
  dec-⊢S Δ nil (γ :: a) = inr λ Δ⊢γ:⊘ → cons≠nil (Δ⊢γ:⊘→γ=nil Δ⊢γ:⊘)
  dec-⊢S Δ (Γ :: (x , A)) (γ :: (y , t)) with dec-⊢S Δ Γ γ | dec-⊢C (Γ :: (x , A)) | dec-⊢t Δ (A [ γ ]Pre-Ty) t | eqdecℕ x y
  ...                                    | inl Δ⊢γ:Γ       | inl Γ+⊢               | inl Δ⊢t                    | inl idp    = inl (sc Δ⊢γ:Γ Γ+⊢ Δ⊢t)
  ...                                    | inl _           | inl _                 | inl _                      | inr x≠y    = inr λ Δ⊢γ+:Γ+ → x≠y (Δ⊢γ+:Γ+→x=y Δ⊢γ+:Γ+)
  ...                                    | inl _           | inl _                 | inr Δ⊬t                    | _          = inr λ Δ⊢γ+:Γ+ → Δ⊬t (Δ⊢γ+:Γ+→Δ⊢t Δ⊢γ+:Γ+)
  ...                                    | inl _           | inr Γ+⊬               | _                          | _          = inr λ Δ⊢γ+:Γ+ → Γ+⊬ (Δ⊢γ:Γ→Γ⊢ Δ⊢γ+:Γ+)
  ...                                    | inr Δ⊬γ         | _                     | _                          | _          = inr λ Δ⊢γ+:Γ+ → Δ⊬γ (Δ⊢γ+:Γ+→Δ⊢γ Δ⊢γ+:Γ+)

  -- ## uniqueness of derivations (all the types are propositions.)
  -- there is a catch here : I should use without-K, I think

  -- elimination of the rules
  -- cc= : ∀ {Γ x A} {Γ⊢ : Γ ⊢C} {Γ⊢' : Γ ⊢C} {x∉Γ : x ∉ Γ} {x∉'Γ : x ∉ Γ} {Γ⊢A : Γ ⊢T A} {Γ⊢'A : Γ ⊢T A} → Γ⊢ == Γ⊢' → x∉Γ == x∉'Γ → Γ⊢A == Γ⊢'A → (cc Γ⊢ x∉Γ Γ⊢A )== (cc Γ⊢' x∉'Γ Γ⊢'A)
  -- cc= idp idp idp = idp

  -- is-prop-⊢C : ∀ {Γ} → is-prop (Γ ⊢C)
  -- is-prop-⊢T : ∀ {Γ A} → is-prop (Γ ⊢T A)
  -- is-prop-⊢t : ∀ {Γ A t} → is-prop (Γ ⊢t t # A)
  -- is-prop-⊢S : ∀ {Δ Γ γ} → is-prop (Δ ⊢S γ > Γ)

  -- fst (is-prop-⊢C ec ec) = idp
  -- snd (is-prop-⊢C ec ec) idp = idp
    -- fst (is-prop-⊢C (cc Γ⊢ x∉Γ Γ⊢A) (cc Γ⊢' x∉'Γ Γ⊢'A)) = cc= (fst (is-prop-⊢C _ _)) {!!} (fst (is-prop-⊢T _ _))
  -- snd (is-prop-⊢C (cc Γ⊢ x∉Γ Γ⊢A) (cc Γ⊢' x∉'Γ Γ⊢'A)) y = {!!}



  -- ## Typed syntax
  Ctx : Set
  Ctx = Σ Pre-Ctx (λ Γ → Γ ⊢C)

  Ty : Ctx → Set
  Ty (Γ , _) = Σ Pre-Ty (λ A → Γ ⊢T A)

  Tm : ∀ (Γ : Ctx) → Ty Γ → Set
  Tm (Γ , _) (A , _) = Σ Pre-Tm (λ t → Γ ⊢t t # A)

  Sub : ∀ (Δ : Ctx) (Γ : Ctx) → Set
  Sub (Δ , _) (Γ , _) = Σ Pre-Sub (λ γ → Δ ⊢S γ > Γ)

 -- ## Operations of typed syntax 
  _∙_ : ∀ (Γ : Ctx) → Ty Γ → Ctx
  (Γ , Γ⊢) ∙ (A , Γ⊢A) = (Γ :: ((length Γ) , A )) , cc Γ⊢ Γ⊢A

-- TODO : define all operation on typed syntax



