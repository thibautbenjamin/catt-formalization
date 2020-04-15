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
  _⊢C : Pre-Ctx → Set
  _⊢T_ : Pre-Ctx → Pre-Ty → Set
  _⊢t_#_ : Pre-Ctx → Pre-Tm → Pre-Ty → Set
  _⊢S_>_ : Pre-Ctx → Pre-Sub → Pre-Ctx → Set

  nil ⊢C = ⊤
  (Γ :: (x , A)) ⊢C = (Γ ⊢C) × ((x ∉ Γ) × (Γ ⊢T A))

  Γ ⊢T Pre-∗ = Γ ⊢C
  Γ ⊢T (Pre-⇒ A t u) =  (Γ ⊢t t # A) × (Γ ⊢t u # A)

  Γ ⊢t (Pre-Var x) # A =  (Γ ⊢C) × (x # A ∈ Γ)

  Δ ⊢S nil > nil = Δ ⊢C
  _ ⊢S nil > (_ :: _) = ⊥
  _ ⊢S (_ :: _) > nil = ⊥
  Δ ⊢S (γ :: (w , t)) > (Γ :: (v , A))  =  (Δ ⊢S γ > Γ)  × (((Γ :: (v , A)) ⊢C) × ((Δ ⊢t t # (A [ γ ]Pre-Ty)) × (v == w)))


  -- ## Properties of the type theory ##
  -- weakening admissibility
  wkT : ∀ {Γ A y B} → Γ ⊢T A → (Γ :: (y , B)) ⊢C → (Γ :: (y , B)) ⊢T A
  wkt : ∀ {Γ A t y B} → Γ ⊢t t # A → (Γ :: (y , B)) ⊢C → (Γ :: (y , B)) ⊢t t # A

  wkT {A = Pre-∗} Γ⊢A Γ,y:B⊢ = Γ,y:B⊢
  wkT {A = Pre-⇒ A t u} (Γ⊢t:A , Γ⊢u:A) Γ,y:B⊢ = wkt Γ⊢t:A Γ,y:B⊢ , wkt Γ⊢u:A Γ,y:B⊢
  wkt {t = Pre-Var x} Γ⊢t:A Γ,y:B⊢ = Γ,y:B⊢ , inl (snd Γ⊢t:A)

  wkS : ∀ {Δ Γ γ y B} → Δ ⊢S γ > Γ → (Δ :: (y , B)) ⊢C → (Δ :: (y , B)) ⊢S γ > Γ
  wkS {Γ = nil} {nil} Δ⊢γ:Γ Δ,y:B⊢ = Δ,y:B⊢
  wkS {Γ = Γ :: (x , A)} {γ :: (x₁ , t)} {y = y} Δ⊢γ:Γ Δ,y:B⊢ = wkS {γ = γ} {y = y} (fst (Δ⊢γ:Γ)) Δ,y:B⊢ , (fst (snd (Δ⊢γ:Γ)) , (wkt {y = y} (fst (snd (snd Δ⊢γ:Γ))) Δ,y:B⊢  , snd (snd (snd Δ⊢γ:Γ))))


  -- Consistency : all objects appearing in derivable judgments are derivable
  Γ⊢A→Γ⊢ : ∀ {Γ A} → Γ ⊢T A → Γ ⊢C
  Γ⊢t:A→Γ⊢ : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢C

  Γ⊢A→Γ⊢ {Γ} {Pre-∗} H = H
  Γ⊢A→Γ⊢ {Γ} {(Pre-⇒ A t u)} H = Γ⊢t:A→Γ⊢ (fst H)

  Γ⊢t:A→Γ⊢ {t = Pre-Var x} H = fst H

  Δ⊢γ:Γ→Γ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Γ ⊢C
  Δ⊢γ:Γ→Γ⊢ {Δ} {nil} {γ} _ = tt
  Δ⊢γ:Γ→Γ⊢ {Δ} {Γ :: a} {γ :: a₁} H = fst (snd H)

  Δ⊢γ:Γ→Δ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Δ ⊢C
  Δ⊢γ:Γ→Δ⊢ {Δ} {nil} {nil} H = H
  Δ⊢γ:Γ→Δ⊢ {Δ} {Γ :: a} {γ :: a₁} H = Δ⊢γ:Γ→Δ⊢ {Δ} {Γ} {γ} (fst H)

  Γ,x:A⊢→Γ,x:A⊢A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢T A
  Γ,x:A⊢→Γ,x:A⊢A {Γ} {x} {A} H = wkT {A = A} {y = x} (snd (snd H)) H

  Γ,x:A⊢→Γ,x:A⊢x:A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢t (Pre-Var x) # A
  Γ,x:A⊢→Γ,x:A⊢x:A H = H , inr (idp , idp)

  Γ⊢t:A→Γ⊢A : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢T A
  Γ⊢t:A→Γ⊢A {Γ :: (v , B)} {A} {Pre-Var x} (Γ,v:B⊢C , inl x:A∈Γ) = wkT {A = A} {y = v} (Γ⊢t:A→Γ⊢A {Γ} {A} {Pre-Var x} ((fst (Γ,v:B⊢C) , x:A∈Γ))) (Γ,v:B⊢C)
  Γ⊢t:A→Γ⊢A {Γ :: (v , B)} {A} {Pre-Var x} (Γ,v:B⊢C , inr x=v×A=B) = coe (ap (λ C → (Γ :: (v , B)) ⊢T C) ((snd (x=v×A=B))^)) (Γ,x:A⊢→Γ,x:A⊢A {A = B} (Γ,v:B⊢C))


  -- ## cut-admissibility ##
  -- notational shortcut : if A = B a term of type A is also of type B
  trT : ∀ {Γ A B t} → A == B → Γ ⊢t t # A → Γ ⊢t t # B
  trT idp Γ⊢t:A = Γ⊢t:A

  -- action on weakened types and terms :
  -- if x is not in A, then A[<γ,(x,t)>] = A[γ] and similarly for terms
  wk[]T : ∀ {Γ Δ γ x u A B} → Γ ⊢T A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (A [ (γ :: (x , u)) ]Pre-Ty) == (A [ γ ]Pre-Ty)
  wk[]t : ∀ {Γ Δ γ x u A t B} → Γ ⊢t t # A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (t [ (γ :: (x , u)) ]Pre-Tm) == (t [ γ ]Pre-Tm)

  wk[]T {A = Pre-∗} Γ⊢A Δ⊢γ+:Γ+ = idp
  wk[]T {A = Pre-⇒ A t u} (Γ⊢t:A , Γ⊢u:A) Δ⊢γ+:Γ+ = Pre-⇒= (wk[]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ+:Γ+) (wk[]t Γ⊢t:A Δ⊢γ+:Γ+) (wk[]t Γ⊢u:A Δ⊢γ+:Γ+)
  wk[]t {x = x} {t = Pre-Var v} Γ⊢v:A Δ⊢γ+:Γ+ with (eqdec𝕍 v x)
  ...                                          | inr _ = idp
  wk[]t {x = .v} {A = _} {Pre-Var v} (_ , v∈Γ) (_ ,((_ ,(v∉Γ , _)) , _)) | inl idp = ⊥-elim (¬∈ v∈Γ v∉Γ)

  -- cut-admissibility : action of substitutions preserves derivability
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)

  []T {Γ} {Pre-∗} {Δ} {γ} Γ⊢A Δ⊢γ:Γ = Δ⊢γ:Γ→Δ⊢ {γ = γ} Δ⊢γ:Γ
  []T {Γ} {Pre-⇒ A t u} {Δ} {γ} (Γ⊢t:A , Γ⊢u:A) Δ⊢γ:Γ = []t Γ⊢t:A Δ⊢γ:Γ  , []t Γ⊢u:A Δ⊢γ:Γ

  []t {nil} {A} {Pre-Var x} {Δ} {nil} (_ , ()) Δ⊢γ:Γ
  []t {Γ :: a} {A} {Pre-Var x} {Δ} {nil} _ ()
  []t {Γ :: (z , B)} {A} {Pre-Var x} {Δ} {γ :: (y , t)} (Γ,y:B⊢ , inl x∈Γ) Δ⊢γ:Γ with (eqdec𝕍 x y )
  []t {Γ :: (.x , B)} {A} {Pre-Var x} {Δ} {γ :: (.x , t)} ((_ ,(x∉Γ , _)) , inl x∈Γ) (_ , (_ , (_ , idp))) | inl idp = ⊥-elim (¬∈ x∈Γ x∉Γ)
  []t {Γ :: (y , B)} {A} {Pre-Var x} {Δ} {γ :: (.y , t)} ((Γ⊢ , _) , inl x∈Γ) Δ⊢γ+:Γ+@(Δ⊢γ:Γ , (_ , (Δ⊢t:B[γ] , idp))) | inr _ =
         trT (wk[]T (Γ⊢t:A→Γ⊢A (Γ⊢ , x∈Γ)) Δ⊢γ+:Γ+ ^)
             ([]t {t = Pre-Var x} {γ = γ} (Γ⊢ , x∈Γ) Δ⊢γ:Γ)
  []t {Γ :: (z , B)} {A} {Pre-Var x} {Δ} {γ :: (y , t)} (Γ,y:B⊢ , inr (x=z , A=B)) Δ⊢γ:Γ with (eqdec𝕍 x y)
  []t {Γ :: (.x , B)} {.B} {Pre-Var x} {Δ} {γ :: (.x , t)} (Γ,y:B⊢ , inr (idp , idp)) (_ , (_ , (_ , idp))) | inr x≠y =  ⊥-elim (x≠y idp)
  []t {Γ :: (.x , B)} {.B} {Pre-Var x} {Δ} {γ :: (.x , t)} ((_ ,(_ , Γ⊢B)) , inr (idp , idp)) Δ⊢γ+:Γ+@(Δ⊢γ:Γ , (_ , (Δ⊢t:B[γ] , idp))) | inl idp =  trT (wk[]T Γ⊢B Δ⊢γ+:Γ+ ^) Δ⊢t:B[γ]


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
  Γ⊢id:Γ {nil} _ = tt
  Γ⊢id:Γ {Γ :: (x , A)} Γ⊢ = wkS {γ = Pre-id Γ} {y = x} (Γ⊢id:Γ (fst Γ⊢)) Γ⊢ , (Γ⊢ , ((Γ⊢ , inr (idp , [id]T Γ A)) , idp))

  -- composition on the pre-syntax
  _∘_ : Pre-Sub → Pre-Sub → Pre-Sub
  nil ∘ γ = nil
  (γ :: (x , t)) ∘ δ = (γ ∘ δ) :: (x , (t [ δ ]Pre-Tm))

  -- action of substitutions on types and terms respects composition
  -- this is only true for well-formed types, terms and substitutions
  [∘]T : ∀ {Γ Δ Θ A γ δ} → Γ ⊢T A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((A [ γ ]Pre-Ty) [ δ ]Pre-Ty) == (A [ γ ∘ δ ]Pre-Ty)
  [∘]t : ∀ {Γ Δ Θ A t γ δ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((t [ γ ]Pre-Tm) [ δ ]Pre-Tm) == (t [ γ ∘ δ ]Pre-Tm)

  [∘]T {A = Pre-∗} _ _ _ = idp
  [∘]T {A = Pre-⇒ A t u} (Γ⊢t:A , Γ⊢u:A) Δ⊢γ:Γ Θ⊢δ:Δ = Pre-⇒= ([∘]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢t:A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢u:A Δ⊢γ:Γ Θ⊢δ:Δ)
  [∘]t {nil} {t = Pre-Var x} {nil} (_ ,()) Δ⊢γ:Γ Θ⊢δ:Δ
  [∘]t {Γ :: _} {t = Pre-Var x} {nil} Γ⊢x:A () Θ⊢δ:Δ
  [∘]t {Γ :: (y , B)} {t = Pre-Var x} {γ :: (v , u)} (Γ,y:B⊢ , Γ,y:B⊢x:A) Δ⊢γ:Γ Θ⊢δ:Δ with (eqdec𝕍 x v)
  ...                                                                                 | inl idp = idp
  [∘]t {Γ :: (y , B)} {A = _} {Pre-Var x} {γ :: (v , u)} (Γ,y:B⊢ , inl x∈Γ) (Δ⊢γ:Γ , _) Θ⊢δ:Δ | inr _ = [∘]t {t = Pre-Var x} {γ = γ} (fst Γ,y:B⊢ , x∈Γ) Δ⊢γ:Γ Θ⊢δ:Δ
  [∘]t {Γ :: (y , B)} {A = _} {Pre-Var x} {γ :: (v , u)} (Γ,y:B⊢ , inr (idp , _)) (Δ⊢γ:Γ , (_ ,(_ , idp))) Θ⊢δ:Δ | inr (x≠v) = ⊥-elim (x≠v idp)


  -- composition of well-formed substitutions is well-formed
  ∘-admissibility : ∀ {Γ Δ Θ γ δ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Θ ⊢S (γ ∘ δ) > Γ
  ∘-admissibility {nil} {Δ} {Θ} {nil} {δ} Δ⊢γ:Γ Θ⊢δ:Δ = Δ⊢γ:Γ→Δ⊢ {Θ} {Δ} {δ} Θ⊢δ:Δ
  ∘-admissibility {Γ :: (x , A)} {Δ} {Θ} {γ :: (y , t)} {δ} (Δ⊢γ:Γ ,(Γ,x:A⊢ ,(Δ⊢t:A[γ] , idp))) Θ⊢δ:Δ = ∘-admissibility {γ = γ} {δ} Δ⊢γ:Γ Θ⊢δ:Δ , (Γ,x:A⊢ , (trT ([∘]T (snd (snd (Γ,x:A⊢))) Δ⊢γ:Γ Θ⊢δ:Δ) ([]t Δ⊢t:A[γ] Θ⊢δ:Δ) , idp))

  -- composition is associative, this is true only for well-formed substitutions
  ∘-associativity : ∀ {Γ Δ Θ Ξ γ δ θ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Ξ ⊢S θ > Θ → ((γ ∘ δ) ∘ θ) == (γ ∘ (δ ∘ θ))
  ∘-associativity {γ = nil} _ _ _ = idp
  ∘-associativity {Γ :: (y , A)} {γ = γ :: (x , t)} (Δ⊢γ:Γ , (_ , (Δ⊢t:A[γ] , idp))) Θ⊢δ:Δ Ξ⊢θ:Θ = ::= (∘-associativity Δ⊢γ:Γ Θ⊢δ:Δ Ξ⊢θ:Θ) ((×= idp ([∘]t Δ⊢t:A[γ] Θ⊢δ:Δ Ξ⊢θ:Θ)))

  -- To prove right-unitality, we need a analoguous of wk[]T and wk[]t for substitutions
  -- Composing if θ is a subst without x, acting (γ :: (x , u)) on it is same as acting just γ on it
  wk[]S : ∀ {Γ Δ γ x u B Θ θ} → Γ ⊢S θ > Θ → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (θ ∘ (γ :: (x , u))) == (θ ∘ γ)
  wk[]S {θ = nil} Γ⊢θ:Θ Δ⊢γ+:Γ+ = idp
  wk[]S {Θ = Θ :: (y , A)} {θ :: (.y , t)} (Γ⊢θ:Θ , (_ , (Γ⊢t:A[θ] , idp))) Δ⊢γ+:Γ+ = ::= (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+) (×= idp (wk[]t Γ⊢t:A[θ] Δ⊢γ+:Γ+))

  ∘-left-unit : ∀{Γ Δ γ} → Δ ⊢S γ > Γ → (Pre-id Γ ∘ γ) == γ
  ∘-left-unit {nil} {Δ} {nil} Δ⊢γ:Γ = idp
  ∘-left-unit {Γ :: (x , A)} {Δ} {γ :: (.x , t)} Δ⊢γ+:Γ+@(Δ⊢γ:Γ , ((Γ⊢ , _) , (_ , idp))) with (eqdec𝕍 x x)
  ...                                                                     | inl idp = ::= (wk[]S (Γ⊢id:Γ Γ⊢) Δ⊢γ+:Γ+ >> ∘-left-unit Δ⊢γ:Γ) idp
  ...                                                                     | inr x≠x = ⊥-elim (x≠x idp)

  -- for some reason right unitality is valid on the presyntax, without well-formedness hypothesis
  ∘-right-unit : ∀{Δ γ} →  (γ ∘ Pre-id Δ) == γ
  ∘-right-unit {Δ} {nil} = idp
  ∘-right-unit {Δ} {γ :: (y , t)} = ::= ∘-right-unit (×= idp ([id]t Δ t))

 -- uniqueness of derivations (all the types are propositions.)
