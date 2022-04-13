{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Syntax

{- Syntax for a globular type theory, with arbitrary term constructors -}
module Globular-TT.Syntax {l} (index : Set l) where

  data Pre-Ty : Set (lsuc l)
  data Pre-Tm : Set (lsuc l)
  data Pre-Sub : Set (lsuc l)
  data Pre-Ctx : Set (lsuc l)

  data Pre-Ty where
    ∗ : Pre-Ty
    _⇒[_]_ : Pre-Tm → Pre-Ty → Pre-Tm → Pre-Ty

  infix 50 _⇒[_]_

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

  -- Equality elimination
  ⇒= : ∀ {A B t t' u u'} → A == B → t == t' → u == u' → t ⇒[ A ] u == t' ⇒[ B ] u'
  ⇒= idp idp idp = idp

  =⇒ : ∀ {A B t t' u u'} → t ⇒[ A ] u == t' ⇒[ B ] u' → ((A == B) × (t == t')) × (u == u')
  =⇒ idp = (idp , idp) , idp

  Var= : ∀ {v w} → v == w → Var v == Var w
  Var= idp = idp

  Tm-constructor= : ∀ {i j γ δ} → i == j → γ == δ → (Tm-constructor i γ) == (Tm-constructor j δ)
  Tm-constructor= idp idp = idp

  =Tm-constructor : ∀ {i j γ δ} → (Tm-constructor i γ) == (Tm-constructor j δ) → i == j × γ == δ
  =Tm-constructor idp = idp , idp

  <,>= : ∀ {γ δ x y t u} → γ == δ → x == y → t == u → < γ , x ↦ t > == < δ , y ↦ u >
  <,>= idp idp idp = idp

  =<,> : ∀ {γ δ x y t u} → < γ , x ↦ t > == < δ , y ↦ u > → ((γ == δ) × (x == y)) × (t == u)
  =<,> idp = (idp , idp) , idp

  ∙= : ∀ {Γ Δ x y A B} → Γ == Δ → x == y → A == B → (Γ ∙ x # A) == (Δ ∙ y # B)
  ∙= idp idp idp = idp


  {- Action of substitutions on types and terms and substitutions on a syntactical level -}
  _[_]Pre-Ty : Pre-Ty → Pre-Sub → Pre-Ty
  _[_]Pre-Tm : Pre-Tm → Pre-Sub → Pre-Tm
  _∘_ : Pre-Sub → Pre-Sub → Pre-Sub

  ∗ [ σ ]Pre-Ty = ∗
  (t ⇒[ A ] u) [ σ ]Pre-Ty = (t [ σ ]Pre-Tm) ⇒[ A [ σ ]Pre-Ty ] (u [ σ ]Pre-Tm)
  Var x [ <> ]Pre-Tm = Var x
  Var x [ < σ , v ↦ t > ]Pre-Tm = if x ≡ v then t else ((Var x) [ σ ]Pre-Tm)
  Tm-constructor i γ [ σ ]Pre-Tm = Tm-constructor i (γ ∘ σ)
  <> ∘ γ = <>
  < γ , x ↦ t > ∘ δ = < γ ∘ δ , x ↦ t [ δ ]Pre-Tm >


  _#_∈_ : ℕ → Pre-Ty → Pre-Ctx → Set (lsuc l)
  _ # _ ∈ ⊘ = ⊥
  x # A ∈ (Γ ∙ y # B) = (x # A ∈ Γ) + ((x == y) × (A == B))


  {- dimension of types -}
  dim : Pre-Ty → ℕ
  dim ∗ = O
  dim (t ⇒[ A ] u) = S (dim A)

  dim[] : ∀ (A : Pre-Ty) (γ : Pre-Sub) → dim (A [ γ ]Pre-Ty) == dim A
  dim[] ∗ γ = idp
  dim[] (_ ⇒[ A ] _) γ = S= (dim[] A γ)

  dimC : Pre-Ctx → ℕ
  dimC ⊘ = O
  dimC (Γ ∙ x # A) = max (dimC Γ) (dim A)

  {- Identity and canonical projection -}
  Pre-id : ∀ (Γ : Pre-Ctx) → Pre-Sub
  Pre-id ⊘ = <>
  Pre-id (Γ ∙ x # A) = < Pre-id Γ , x ↦ Var x >

  Pre-π : ∀ (Γ : Pre-Ctx) (x : ℕ) (A : Pre-Ty) → Pre-Sub
  Pre-π Γ x A = Pre-id Γ


  {- Translation of GSeTT to a globular-TT -}
  GPre-Ctx : GSeTT.Syntax.Pre-Ctx → Pre-Ctx
  GPre-Ty : GSeTT.Syntax.Pre-Ty → Pre-Ty
  GPre-Tm : GSeTT.Syntax.Pre-Tm → Pre-Tm

  GPre-Ctx nil = ⊘
  GPre-Ctx (Γ :: (x , A)) = (GPre-Ctx Γ) ∙ x # (GPre-Ty A)
  GPre-Ty GSeTT.Syntax.∗ = ∗
  GPre-Ty (t GSeTT.Syntax.⇒[ A ] u) = (GPre-Tm t) ⇒[ GPre-Ty A ] (GPre-Tm u)
  GPre-Tm (GSeTT.Syntax.Var x) = Var x

  {- Depth of a term -}
  depth : Pre-Tm → ℕ
  depthS : Pre-Sub → ℕ

  depth (Var x) = O
  depth (Tm-constructor i γ) = S (depthS γ)

  depthS <> = O
  depthS < γ , x ↦ t > = max (depthS γ) (depth t)
