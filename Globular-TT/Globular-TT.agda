{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Syntax
import GSeTT.Rules
open import GSeTT.Typed-Syntax

module Globular-TT.Syntax (index : Set) (rule : index → Σ GSeTT.Typed-Syntax.Ctx (λ Γ → Ty Γ)) where
  {- Pre-syntax -}
  data Pre-Ty : Set₁
  data Pre-Tm : Set₁
  data Pre-Sub : Set₁
  data Pre-Ctx : Set₁

  data Pre-Ty where
    ∗ : Pre-Ty
    ⇒ : Pre-Ty → Pre-Tm → Pre-Tm → Pre-Ty

  data Pre-Tm where
    Var : ℕ → Pre-Tm
    Tm-constructor : ∀ (i : index) → Pre-Sub → Pre-Tm

  data Pre-Sub where
    <> : Pre-Sub
    <_,_↦_> : Pre-Sub → ℕ → Pre-Tm → Pre-Sub

  data Pre-Ctx where
    ⊘ : Pre-Ctx
    _∙_#_ : Pre-Ctx → ℕ → Pre-Ty → Pre-Ctx

  C-length : Pre-Ctx → ℕ
  C-length ⊘ = O
  C-length (Γ ∙ _ # _) = S (C-length Γ)

  -- Equality elimination for constructors
  ⇒= : ∀ {A B t t' u u'} → A == B → t == t' → u == u' → ⇒ A t u == ⇒ B t' u'
  ⇒= idp idp idp = idp

  Var= : ∀ {v w} → v == w → Var v == Var w
  Var= idp = idp

  Tm-constructor= : ∀ {i j γ δ} → i == j → γ == δ → (Tm-constructor i γ) == (Tm-constructor j δ)
  Tm-constructor= idp idp = idp

  <,>= : ∀ {γ δ x y t u} → γ == δ → x == y → t == u → < γ , x ↦ t > == < δ , y ↦ u >
  <,>= idp idp idp = idp

  ∙= : ∀ {Γ Δ x y A B} → Γ == Δ → x == y → A == B → (Γ ∙ x # A) == (Δ ∙ y # B)
  ∙= idp idp idp = idp

  -- Action of substitutions on types and terms and substitutions on a syntactical level
  _[_]Pre-Ty : Pre-Ty → Pre-Sub → Pre-Ty
  _[_]Pre-Tm : Pre-Tm → Pre-Sub → Pre-Tm
  _∘_ : Pre-Sub → Pre-Sub → Pre-Sub

  ∗ [ σ ]Pre-Ty = ∗
  ⇒ A t u [ σ ]Pre-Ty = ⇒ (A [ σ ]Pre-Ty) (t [ σ ]Pre-Tm) (u [ σ ]Pre-Tm)
  Var x [ <> ]Pre-Tm = Var x
  Var x [ < σ , v ↦ t > ]Pre-Tm = if x ≡ v then t else ((Var x) [ σ ]Pre-Tm)
  Tm-constructor i γ [ σ ]Pre-Tm = Tm-constructor i (γ ∘ σ)
  <> ∘ γ = <>
  < γ , x ↦ t > ∘ δ = < γ ∘ δ , x ↦ t [ δ ]Pre-Tm >


  _#_∈_ : ℕ → Pre-Ty → Pre-Ctx → Set₁
  _ # _ ∈ ⊘ = ⊥
  x # A ∈ (Γ ∙ y # B) = (x # A ∈ Γ) + ((x == y) × (A == B))


  {- Translation of GSeTT to a globular-TT -}
  GPre-Ctx : GSeTT.Syntax.Pre-Ctx → Pre-Ctx
  GPre-Ty : GSeTT.Syntax.Pre-Ty → Pre-Ty
  GPre-Tm : GSeTT.Syntax.Pre-Tm → Pre-Tm

  GPre-Ctx nil = ⊘
  GPre-Ctx (Γ :: (x , A)) = (GPre-Ctx Γ) ∙ x # (GPre-Ty A)
  GPre-Ty GSeTT.Syntax.∗ = ∗
  GPre-Ty (GSeTT.Syntax.⇒ A t u) = ⇒ (GPre-Ty A) (GPre-Tm t) (GPre-Tm u)
  GPre-Tm (GSeTT.Syntax.Var x) = Var x

  -- ## Well-formedness statements ≡ inference rules ##
  data _⊢C : Pre-Ctx → Set₁
  data _⊢T_ : Pre-Ctx → Pre-Ty → Set₁
  data _⊢t_#_ : Pre-Ctx → Pre-Tm → Pre-Ty → Set₁
  data _⊢S_>_ : Pre-Ctx → Pre-Sub → Pre-Ctx → Set₁

  data _⊢C where
    ec : ⊘ ⊢C
    cc : ∀ {Γ A} → Γ ⊢C → Γ ⊢T A → (Γ ∙ (C-length Γ) # A) ⊢C

  data _⊢T_ where
    ob : ∀ {Γ} → Γ ⊢C → Γ ⊢T ∗
    ar : ∀ {Γ A t u} → Γ ⊢t t # A → Γ ⊢t u # A → Γ ⊢T ⇒ A t u

  data _⊢t_#_ where
    var : ∀ {Γ x A} → Γ ⊢C → x # A ∈ Γ → Γ ⊢t (Var x) # A
    tm : ∀ {Δ γ} → (i : index) → Δ ⊢S γ > GPre-Ctx (fst (fst (rule i))) → Δ ⊢t Tm-constructor i γ # ((GPre-Ty (fst (snd (rule i)))) [ γ ]Pre-Ty)

  data _⊢S_>_ where
    es : ∀ {Δ} → Δ ⊢C → Δ ⊢S <> > ⊘
    sc : ∀ {Δ Γ γ x A t} → Δ ⊢S γ > Γ → (Γ ∙ x # A) ⊢C → (Δ ⊢t t # (A [ γ ]Pre-Ty)) → Δ ⊢S < γ , x ↦ t > > (Γ ∙ x # A)


  {- Derivability is preserved by the translation from GSeTT to our TT -}
  x∈GCtx : ∀ {x A Γ} → x GSeTT.Syntax.# A ∈ Γ → x # GPre-Ty A ∈ GPre-Ctx Γ
  x∈GCtx {Γ = Γ :: a} (inl x∈Γ) = inl (x∈GCtx x∈Γ)
  x∈GCtx {Γ = Γ :: (x,A)} (inr (idp , idp)) = inr (idp , idp)


  GCtx : ∀ (Γ : GSeTT.Syntax.Pre-Ctx) → Γ GSeTT.Rules.⊢C → (GPre-Ctx Γ) ⊢C
  GTy : ∀ (Γ : GSeTT.Syntax.Pre-Ctx) (A : GSeTT.Syntax.Pre-Ty) → Γ GSeTT.Rules.⊢T A → (GPre-Ctx Γ) ⊢T (GPre-Ty A)
  GTm : ∀ (Γ : GSeTT.Syntax.Pre-Ctx) (A : GSeTT.Syntax.Pre-Ty) (t : GSeTT.Syntax.Pre-Tm) → Γ GSeTT.Rules.⊢t t # A  → (GPre-Ctx Γ) ⊢t (GPre-Tm t) # (GPre-Ty A)

  GCtx .nil GSeTT.Rules.ec = ec
  GCtx .(_ :: (length _ , _)) (GSeTT.Rules.cc Γ⊢ Γ⊢A) = {!cc (GCtx Γ⊢) (GTy Γ⊢A)!}
  GTy Γ .GSeTT.Syntax.∗ (GSeTT.Rules.ob Γ⊢) = ob (GCtx Γ Γ⊢)
  GTy Γ (GSeTT.Syntax.⇒ A t u) (GSeTT.Rules.ar Γ⊢t:A Γ⊢u:A) = ar (GTm Γ A t Γ⊢t:A) (GTm Γ A u Γ⊢u:A)
  GTm Γ A (GSeTT.Syntax.Var x) (GSeTT.Rules.var Γ⊢ x∈Γ) = var (GCtx Γ Γ⊢) (x∈GCtx x∈Γ)


  -- ## Properties of the type theory ##
  -- weakening admissibility
  wkT : ∀ {Γ A y B} → Γ ⊢T A → (Γ ∙ y # B) ⊢C → (Γ ∙ y # B) ⊢T A
  wkt : ∀ {Γ A t y B} → Γ ⊢t t # A → (Γ ∙ y # B) ⊢C → (Γ ∙ y # B) ⊢t t # A
  wkS : ∀ {Δ Γ γ y B} → Δ ⊢S γ > Γ → (Δ ∙ y # B) ⊢C → (Δ ∙ y # B) ⊢S γ > Γ

  wkT (ob _) Γ,y:B⊢ = ob Γ,y:B⊢
  wkT (ar Γ⊢t:A Γ⊢u:A) Γ,y:B⊢ = ar (wkt Γ⊢t:A Γ,y:B⊢) (wkt Γ⊢u:A Γ,y:B⊢)
  wkt (var Γ⊢C x∈Γ) Γ,y:B⊢ = var Γ,y:B⊢ (inl x∈Γ)
  wkt (tm i Γ⊢γ:Δ) Γ,y:B⊢ = tm i (wkS Γ⊢γ:Δ Γ,y:B⊢)
  wkS (es _) Δ,y:B⊢ = es Δ,y:B⊢
  wkS (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) Δ,y:B⊢ = sc (wkS Δ⊢γ:Γ Δ,y:B⊢) Γ,x:A⊢ (wkt Δ⊢t:A[γ] Δ,y:B⊢)


  -- Consistency : all objects appearing in derivable judgments are derivable
  Γ⊢A→Γ⊢ : ∀ {Γ A} → Γ ⊢T A → Γ ⊢C
  Γ⊢t:A→Γ⊢ : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢C
  Δ⊢γ:Γ→Δ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Δ ⊢C

  Γ⊢A→Γ⊢ (ob Γ⊢) = Γ⊢
  Γ⊢A→Γ⊢ (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A→Γ⊢ Γ⊢t:A
  Γ⊢t:A→Γ⊢ (var Γ⊢ _) = Γ⊢
  Γ⊢t:A→Γ⊢ (tm i Γ⊢γ:Δ) = Δ⊢γ:Γ→Δ⊢ Γ⊢γ:Δ
  Δ⊢γ:Γ→Δ⊢ (es Δ⊢) = Δ⊢
  Δ⊢γ:Γ→Δ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ

  Δ⊢γ:Γ→Γ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Γ ⊢C
  Δ⊢γ:Γ→Γ⊢ (es Δ⊢) = ec
  Δ⊢γ:Γ→Γ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Γ,x:A⊢



  Γ,x:A⊢→Γ,x:A⊢A : ∀ {Γ x A} → (Γ ∙ x # A) ⊢C → (Γ ∙ x # A) ⊢T A
  Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = wkT Γ⊢A Γ,x:A⊢

  Γ,x:A⊢→Γ,x:A⊢x:A : ∀ {Γ x A} → (Γ ∙ x # A) ⊢C → (Γ ∙ x # A) ⊢t (Var x) # A
  Γ,x:A⊢→Γ,x:A⊢x:A Γ,x:A⊢ = var Γ,x:A⊢ (inr (idp , idp))

  Γ⊢t:A→Γ⊢A : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢T A
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc Γ⊢ Γ⊢A) (inl y∈Γ)) = wkT (Γ⊢t:A→Γ⊢A (var Γ⊢ y∈Γ)) Γ,x:A⊢
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc _ _) (inr (idp , idp))) = Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢
  -- this one is slightly harder
  Γ⊢t:A→Γ⊢A (tm i _) = {!GTy!}

  -- ## cut-admissibility ##
  -- notational shortcut : if A = B a term of type A is also of type B
  trT : ∀ {Γ A B t} → A == B → Γ ⊢t t # A → Γ ⊢t t # B
  trT idp Γ⊢t:A = Γ⊢t:A

  -- action on weakened types and terms :
  -- if x is not in A, then A[<γ,(x,t)>] = A[γ] and similarly for terms
  n∉Γ : ∀ {Γ A n} → Γ ⊢C → (C-length Γ ≤ n) → ¬ (n # A ∈ Γ)
  n∉Γ (cc Γ⊢ _) l+1≤n (inl n∈Γ) = n∉Γ Γ⊢ (Sn≤m→n≤m l+1≤n) n∈Γ
  n∉Γ (cc Γ⊢ _) Sn≤n (inr (idp , idp)) = Sn≰n _ Sn≤n

  lΓ∉Γ : ∀ {Γ A} → Γ ⊢C → ¬ ((C-length Γ) # A ∈ Γ)
  lΓ∉Γ Γ⊢ = n∉Γ Γ⊢ (n≤n _)

  wk[]T : ∀ {Γ Δ γ x u A B} → Γ ⊢T A → Δ ⊢S < γ , x ↦ u > > (Γ ∙ x # B) → (A [ < γ , x ↦ u > ]Pre-Ty) == (A [ γ ]Pre-Ty)
  wk[]t : ∀ {Γ Δ γ x u A t B} → Γ ⊢t t # A → Δ ⊢S < γ , x ↦ u > > (Γ ∙ x # B) → (t [ < γ , x ↦ u > ]Pre-Tm) == (t [ γ ]Pre-Tm)
  wk[]S : ∀ {Γ Δ γ x u B Θ θ} → Γ ⊢S θ > Θ → Δ ⊢S < γ , x ↦ u > > (Γ ∙ x # B) → (θ ∘ < γ , x ↦ u >) == (θ ∘ γ)

  wk[]T (ob Γ⊢) _ = idp
  wk[]T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ+:Γ+ = ⇒= (wk[]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ+:Γ+)  (wk[]t Γ⊢t:A Δ⊢γ+:Γ+) (wk[]t Γ⊢u:A Δ⊢γ+:Γ+)
  wk[]t {x = x} (var {x = y} Γ⊢ y∈Γ) Δ⊢γ+:Γ+             with (eqdecℕ y x)
  ...                                                    | inr _ = idp
  wk[]t (var Γ⊢ l∈Γ) (sc Δ⊢γ:Γ (cc _ _) _) | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ l∈Γ)
  wk[]t (tm i Γ⊢θ:Θ) Δ⊢γ+:Γ+ = Tm-constructor= idp (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+)
  wk[]S (es _) _ = idp
  wk[]S (sc Γ⊢θ:Θ _ Γ⊢t:A[θ]) Δ⊢γ+:Γ+ = {!!} -- ::= (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+)  (×= idp (wk[]t Γ⊢t:A[θ] Δ⊢γ+:Γ+))



  {- cut-admissibility : action of substitutions preserves derivability -}
  -- Compared to GSeTT, these proofs are more mutually inductive
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)
  [∘]T : ∀ {Γ Δ Θ A γ δ} → Γ ⊢T A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((A [ γ ]Pre-Ty) [ δ ]Pre-Ty) == (A [ γ ∘ δ ]Pre-Ty)
  [∘]t : ∀ {Γ Δ Θ A t γ δ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((t [ γ ]Pre-Tm) [ δ ]Pre-Tm) == (t [ γ ∘ δ ]Pre-Tm)
  ∘-admissibility : ∀ {Γ Δ Θ γ δ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Θ ⊢S (γ ∘ δ) > Γ
  ∘-associativity : ∀ {Γ Δ Θ Ξ γ δ θ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Ξ ⊢S θ > Θ → ((γ ∘ δ) ∘ θ) == (γ ∘ (δ ∘ θ))


  []T (ob Γ⊢) Δ⊢γ:Γ = ob (Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ)
  []T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ = ar ([]t Γ⊢t:A Δ⊢γ:Γ) ([]t Γ⊢u:A Δ⊢γ:Γ)
  []t {t = .(Tm-constructor i _)} (tm i x) Δ⊢γ:Γ = trT ([∘]T (GTy _ _ (snd (snd (rule i)))) x Δ⊢γ:Γ ^) (tm i (∘-admissibility x Δ⊢γ:Γ))
  []t {Γ = (Γ ∙ _ # _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ _) (inl x∈Γ)) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ _ _) with (eqdecℕ x (C-length Γ))
  ...                                                                                     | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  ...                                                                                     | inr _ = trT (wk[]T (Γ⊢t:A→Γ⊢A (var Γ⊢ x∈Γ)) Δ⊢γ+:Γ+ ^) ([]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ)
  []t {Γ = (Γ ∙ _ # _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ Γ⊢A) (inr (idp , idp))) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ x₁ Δ⊢t:A[γ]) with (eqdecℕ x (C-length Γ))
  ...                                                                                     | inl idp = trT (wk[]T Γ⊢A Δ⊢γ+:Γ+ ^) Δ⊢t:A[γ]
  ...                                                                                     | inr x≠x = ⊥-elim (x≠x idp)


  [∘]T (ob _) _ _ = idp
  [∘]T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ Θ⊢δ:Δ = ⇒= ([∘]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢t:A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢u:A Δ⊢γ:Γ Θ⊢δ:Δ)
  [∘]t (tm i x) Δ⊢γ:Γ Θ⊢δ:Δ = Tm-constructor= idp (∘-associativity x Δ⊢γ:Γ Θ⊢δ:Δ )
  [∘]t (var {x = x} Γ,y:A⊢ x∈Γ+) (sc {x = y} Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ with (eqdecℕ x y )
  ...                                                                | inl idp = idp
  [∘]t (var Γ,y:A⊢ (inr (idp , idp))) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr x≠x = ⊥-elim (x≠x idp)
  [∘]t (var (cc Γ⊢ _) (inl x∈Γ)) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr _ = [∘]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ Θ⊢δ:Δ

  ∘-admissibility (es Δ⊢) Θ⊢δ:Δ = es (Δ⊢γ:Γ→Δ⊢ Θ⊢δ:Δ)
  ∘-admissibility (sc Δ⊢γ:Γ Γ,x:A⊢@(cc _ Γ⊢A) Δ⊢t:A[γ]) Θ⊢δ:Δ = sc (∘-admissibility Δ⊢γ:Γ Θ⊢δ:Δ) Γ,x:A⊢ (trT ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([]t Δ⊢t:A[γ] Θ⊢δ:Δ))

  ∘-associativity (es _) _ _ = idp
  ∘-associativity (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ Ξ⊢θ:Θ = {!!} -- ::= (∘-associativity Δ⊢γ:Γ Θ⊢δ:Δ Ξ⊢θ:Θ) (×= idp ([∘]t Δ⊢t:A[γ] Θ⊢δ:Δ Ξ⊢θ:Θ))



  -- ## categorical structure ##
  -- identity on the presyntax level
  Pre-id : ∀ (Γ : Pre-Ctx) → Pre-Sub
  Pre-id ⊘ = <>
  Pre-id (Γ ∙ x # A) = < Pre-id Γ , x ↦ Var x >

  -- action of identity on types and terms is trivial on the syntax level
  [id]T : ∀ Γ A → (A [ Pre-id Γ ]Pre-Ty) == A
  [id]t : ∀ Γ t → (t [ Pre-id Γ ]Pre-Tm) == t
  ∘-right-unit : ∀ {Δ γ} →  (γ ∘ Pre-id Δ) == γ

  [id]T Γ ∗ = idp
  [id]T Γ (⇒ A t u) = ⇒= ([id]T Γ A) ([id]t Γ t) ([id]t Γ u)
  [id]t Γ (Tm-constructor i γ) = Tm-constructor= idp ∘-right-unit
  [id]t ⊘ (Var x) = idp
  [id]t (Γ ∙ y # B) (Var x) with (eqdecℕ x y)
  ...                              | inl x=y = Var= (x=y ^)
  ...                              | inr _ = [id]t Γ (Var x)
  ∘-right-unit {Δ} {<>} = idp
  ∘-right-unit {Δ} {< γ , y ↦ t >} = {!!} -- ::= ∘-right-unit (×= idp ([id]t Δ t))



  -- identity is well-formed
  Γ⊢id:Γ : ∀ {Γ} → Γ ⊢C → Γ ⊢S Pre-id Γ > Γ
  Γ⊢id:Γ ec = es ec
  Γ⊢id:Γ Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = sc (wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢) Γ,x:A⊢ (var Γ,x:A⊢ (inr (idp , [id]T _ _)))



  -- composition is associative, this is true only for well-formed substitutions

  ∘-left-unit : ∀{Γ Δ γ} → Δ ⊢S γ > Γ → (Pre-id Γ ∘ γ) == γ
  ∘-left-unit (es _) = idp
  ∘-left-unit Δ⊢γ+:Γ+@(sc {x = x} Δ⊢γ:Γ (cc Γ⊢ _) _) with (eqdecℕ x x)
  ...                                                  | inl idp = {!!} -- ::= (wk[]S (Γ⊢id:Γ Γ⊢) Δ⊢γ+:Γ+ >> ∘-left-unit Δ⊢γ:Γ) idp
  ...                                                  | inr x≠x = ⊥-elim (x≠x idp)




  -- ## Structure of CwF
  Pre-π : ∀ (Γ : Pre-Ctx) (x : ℕ) (A : Pre-Ty) → Pre-Sub
  Pre-π Γ x A = Pre-id Γ

  Γ,x:A⊢π:Γ : ∀ {Γ x A} → (Γ ∙ x # A) ⊢C → (Γ ∙ x # A) ⊢S Pre-π Γ x A > Γ
  Γ,x:A⊢π:Γ Γ,x:A⊢@(cc Γ⊢ _) = wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢
