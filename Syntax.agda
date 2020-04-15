{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude

module Syntax (𝕍 : Set) (eqdec𝕍 : eqdec 𝕍) where

  data list : Set → Set where
    nil : ∀{A} → list A
    _::_ : ∀ {A} → list A → (a : A) → list A

  ::= : ∀ {A} {l l' : list A} {a a' : A} → l == l' → a == a' → (l :: a) == (l' :: a')
  ::= idp idp = idp

  ifdec_>_then_else_ : ∀ {i j} {A : Set i} (B : Set j) → (dec B) → A → A → A
  ifdec b > inl x then A else B = A
  ifdec b > inr x then A else B = B

  if_≡_then_else_ : ∀ {i} {A : Set i} → 𝕍 → 𝕍 → A → A → A
  if v ≡ w then A else B = ifdec (v == w) > (eqdec𝕍 v w) then A else B

  -- Pre-syntax
  data Pre-Ty : Set
  data Pre-Tm : Set

  data Pre-Ty where
    Pre-∗ : Pre-Ty
    Pre-⇒ : Pre-Ty → Pre-Tm → Pre-Tm → Pre-Ty

  data Pre-Tm where
    Pre-Var : 𝕍 → Pre-Tm

  Pre-Ctx : Set
  Pre-Ctx = list (𝕍 × Pre-Ty)

  Pre-Sub : Set
  Pre-Sub = list (𝕍 × Pre-Tm)

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

  -- x ∉ Γ ⇒ the variable x doesn't appear in Γ
  _∉_ : 𝕍 → Pre-Ctx → Set
  v ∉ nil = ⊤
  v ∉ (Γ :: (w , A)) = (v ∉ Γ) × (v ≠ w)


  -- x # A ∈ Γ ⇒ the variable x appears in Γ with type A
  _#_∈_ : 𝕍 → Pre-Ty → Pre-Ctx → Set
  _ # _ ∈ nil = ⊥
  x # A ∈ (Γ :: (y , B)) = (x # A ∈ Γ) + ((x == y) × (A == B))

  -- useful for reasoning, x cannot be both in Γ and not in Γ
  ¬∈ : ∀ {x Γ A} → x # A ∈ Γ → x ∉ Γ → ⊥
  ¬∈ {Γ = Γ :: (y , _)} (inl x∈Γ) (x∉Γ , x≠y) = ¬∈ x∈Γ x∉Γ
  ¬∈ {Γ = Γ :: (y , _)} (inr (x=y , _)) (x∉Γ , x≠y) = x≠y x=y

  -- ## Well-formedness statements ≡ inference rules ##
  data _⊢C : Pre-Ctx → Set
  data _⊢T_ : Pre-Ctx → Pre-Ty → Set
  data _⊢t_#_ : Pre-Ctx → Pre-Tm → Pre-Ty → Set
  data _⊢S_>_ : Pre-Ctx → Pre-Sub → Pre-Ctx → Set

  data _⊢C where
    ec : nil ⊢C
    cc : ∀ {Γ x A} → Γ ⊢C → x ∉ Γ → Γ ⊢T A → (Γ :: (x , A)) ⊢C

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
  Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢@(cc Γ⊢ x∉Γ Γ⊢A) = wkT Γ⊢A Γ,x:A⊢

  Γ,x:A⊢→Γ,x:A⊢x:A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢t (Pre-Var x) # A
  Γ,x:A⊢→Γ,x:A⊢x:A Γ,x:A⊢ = var Γ,x:A⊢ (inr (idp , idp))

  Γ⊢t:A→Γ⊢A : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢T A
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc Γ⊢ x∉Γ Γ⊢A) (inl y∈Γ)) = wkT (Γ⊢t:A→Γ⊢A (var Γ⊢ y∈Γ)) Γ,x:A⊢
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc _ _ _) (inr (idp , idp))) = Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢


  -- ## cut-admissibility ##
  -- notational shortcut : if A = B a term of type A is also of type B
  trT : ∀ {Γ A B t} → A == B → Γ ⊢t t # A → Γ ⊢t t # B
  trT idp Γ⊢t:A = Γ⊢t:A

  -- action on weakened types and terms :
  -- if x is not in A, then A[<γ,(x,t)>] = A[γ] and similarly for terms
  wk[]T : ∀ {Γ Δ γ x u A B} → Γ ⊢T A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (A [ (γ :: (x , u)) ]Pre-Ty) == (A [ γ ]Pre-Ty)
  wk[]t : ∀ {Γ Δ γ x u A t B} → Γ ⊢t t # A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (t [ (γ :: (x , u)) ]Pre-Tm) == (t [ γ ]Pre-Tm)

  wk[]T (ob Γ⊢) _ = idp
  wk[]T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ+:Γ+ = Pre-⇒= (wk[]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ+:Γ+)  (wk[]t Γ⊢t:A Δ⊢γ+:Γ+) (wk[]t Γ⊢u:A Δ⊢γ+:Γ+)
  wk[]t {x = x} (var {x = y} Γ⊢ y∈Γ) Δ⊢γ+:Γ+             with (eqdec𝕍 y x)
  ...                                                    | inr _ = idp
  wk[]t {x = x} (var Γ⊢ x∈Γ) (sc Δ⊢γ+:Γ+ (cc _ x∉Γ _) _) | inl idp = ⊥-elim (¬∈ x∈Γ x∉Γ )


  -- cut-admissibility : action of substitutions preserves derivability
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)

  []T (ob Γ⊢) Δ⊢γ:Γ = ob (Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ)
  []T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ = ar ([]t Γ⊢t:A Δ⊢γ:Γ) ([]t Γ⊢u:A Δ⊢γ:Γ)
  []t (var {x = x} (cc {x = y} Γ⊢ y∉Γ Γ⊢B) (inl x∈Γ)) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ _ Δ⊢t:B[Γ]) with (eqdec𝕍 x y)
  ...                                                                               | inl idp = ⊥-elim (¬∈ x∈Γ y∉Γ)
  ...                                                                               | inr H = trT (wk[]T (Γ⊢t:A→Γ⊢A (var Γ⊢  x∈Γ)) Δ⊢γ+:Γ+ ^) ([]t (var Γ⊢  x∈Γ) Δ⊢γ:Γ)
  []t (var {x = x} (cc Γ⊢ x∉Γ Γ⊢A) (inr (idp , idp))) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ+ _ Δ⊢t:A[γ]) with (eqdec𝕍 x x)
  ...                                                                                | inl idp = trT (wk[]T Γ⊢A Δ⊢γ+:Γ+ ^) Δ⊢t:A[γ]
  ...                                                                                | inr x≠x = ⊥-elim (x≠x idp)


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
  [id]t (Γ :: (y , B)) (Pre-Var x) with (eqdec𝕍 x y)
  ...                              | inl x=y = Pre-Var= (x=y ^)
  ...                              | inr _ = [id]t Γ (Pre-Var x)


  -- identity is well-formed
  Γ⊢id:Γ : ∀ {Γ} → Γ ⊢C → Γ ⊢S Pre-id Γ > Γ
  Γ⊢id:Γ ec = es ec
  Γ⊢id:Γ Γ,x:A⊢@(cc Γ⊢ x∉Γ Γ⊢A) = sc (wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢) Γ,x:A⊢ (var Γ,x:A⊢ (inr (idp , [id]T _ _)))

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
  [∘]t (var {x = x} Γ,y:A⊢ x∈Γ+) (sc {x = y} Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ with (eqdec𝕍 x y )
  ...                                                                | inl idp = idp
  [∘]t (var Γ,y:A⊢ (inr (idp , idp))) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr x≠x = ⊥-elim (x≠x idp)
  [∘]t (var (cc Γ⊢ _ _) (inl x∈Γ)) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr _ = [∘]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ Θ⊢δ:Δ


  -- composition of well-formed substitutions is well-formed
  ∘-admissibility : ∀ {Γ Δ Θ γ δ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Θ ⊢S (γ ∘ δ) > Γ
  ∘-admissibility (es Δ⊢) Θ⊢δ:Δ = es (Δ⊢γ:Γ→Δ⊢ Θ⊢δ:Δ)
  ∘-admissibility (sc Δ⊢γ:Γ Γ,x:A⊢@(cc _ _ Γ⊢A) Δ⊢t:A[γ]) Θ⊢δ:Δ = sc (∘-admissibility Δ⊢γ:Γ Θ⊢δ:Δ) Γ,x:A⊢ (trT ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([]t Δ⊢t:A[γ] Θ⊢δ:Δ))

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
  ∘-left-unit Δ⊢γ+:Γ+@(sc {x = x} Δ⊢γ:Γ (cc Γ⊢ _ _) _) with (eqdec𝕍 x x)
  ...                                                  | inl idp = ::= (wk[]S (Γ⊢id:Γ Γ⊢) Δ⊢γ+:Γ+ >> ∘-left-unit Δ⊢γ:Γ) idp
  ...                                                  | inr x≠x = ⊥-elim (x≠x idp)

  -- for some reason right unitality is valid on the presyntax, without well-formedness hypothesis
  ∘-right-unit : ∀{Δ γ} →  (γ ∘ Pre-id Δ) == γ
  ∘-right-unit {Δ} {nil} = idp
  ∘-right-unit {Δ} {γ :: (y , t)} = ::= ∘-right-unit (×= idp ([id]t Δ t))

 -- uniqueness of derivations (all the types are propositions.)
