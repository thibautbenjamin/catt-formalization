{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude

{- Syntax for the Type theory for globular sets -}
module GSeTT.Syntax where

  data Pre-Ty : Set
  data Pre-Tm : Set

  data Pre-Ty where
    ∗ : Pre-Ty
    ⇒ : Pre-Ty → Pre-Tm → Pre-Tm → Pre-Ty

  data Pre-Tm where
    Var : ℕ → Pre-Tm

  Pre-Ctx : Set₁
  Pre-Ctx = list (ℕ × Pre-Ty)

  Pre-Sub : Set₁
  Pre-Sub = list (ℕ × Pre-Tm)

  ⇒= : ∀ {A B t t' u u'} → A == B → t == t' → u == u' → ⇒ A t u == ⇒ B t' u'
  ⇒= idp idp idp = idp

  Var= : ∀ {v w} → v == w → Var v == Var w
  Var= idp = idp

  {- Dimension of a type and aof a context -}
  -- Careful: dimension of ∗ should be -1
  dim : Pre-Ty → ℕ
  dim ∗ = O
  dim (⇒ A t u) = S (dim A)

  -- Careful: dimension of the empty context should be -1
  dimC : Pre-Ctx → ℕ
  dimC nil = O
  dimC (Γ :: (x , A)) with (dec-≤ (dim A) (dimC Γ))
  ...                         | inl _ = dimC Γ
  ...                         | inr _ = dim A



  {- Action of substitutions on types and terms on a syntactical level -}
  _[_]Pre-Ty : Pre-Ty → Pre-Sub → Pre-Ty
  _[_]Pre-Tm : Pre-Tm → Pre-Sub → Pre-Tm

  ∗ [ σ ]Pre-Ty = ∗
  ⇒ A t u [ σ ]Pre-Ty = ⇒ (A [ σ ]Pre-Ty) (t [ σ ]Pre-Tm) (u [ σ ]Pre-Tm)
  Var x [ nil ]Pre-Tm = Var x
  Var x [ σ :: (v , t) ]Pre-Tm = if x ≡ v then t else ((Var x) [ σ ]Pre-Tm)

  _∘_ : Pre-Sub → Pre-Sub → Pre-Sub
  nil ∘ γ = nil
  (γ :: (x , t)) ∘ δ = (γ ∘ δ) :: (x , (t [ δ ]Pre-Tm))

  {- Identity and canonical projection -}
  Pre-id : ∀ (Γ : Pre-Ctx) → Pre-Sub
  Pre-id nil = nil
  Pre-id (Γ :: (x , A)) = (Pre-id Γ) :: (x , Var x)

  Pre-π : ∀ (Γ : Pre-Ctx) (x : ℕ) (A : Pre-Ty) → Pre-Sub
  Pre-π Γ x A = Pre-id Γ

  {- The pairing (x#A) ∈ Γ  -}
  _#_∈_ : ℕ → Pre-Ty → Pre-Ctx → Set
  _ # _ ∈ nil = ⊥
  x # A ∈ (Γ :: (y , B)) = (x # A ∈ Γ) + ((x == y) × (A == B))

