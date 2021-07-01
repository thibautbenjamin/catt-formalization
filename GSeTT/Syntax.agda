{-# OPTIONS --rewriting --without-K #-}

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

  =⇒ : ∀ {A B t t' u u'} → ⇒ A t u == ⇒ B t' u' → (A == B × t == t') × u == u'
  =⇒ idp = (idp , idp) , idp

  tgt= : ∀ {A B t t' u u'} → ⇒ A t u == ⇒ B t' u' →  u == u'
  tgt= idp = idp

  Var= : ∀ {v w} → v == w → Var v == Var w
  Var= idp = idp

  =Var : ∀ {v w} → Var v == Var w → v == w
  =Var idp = idp

  {- Dimension of a type and aof a context -}
  -- Careful: dimension of ∗ should be -1
  dim : Pre-Ty → ℕ
  dim ∗ = O
  dim (⇒ A t u) = S (dim A)

  -- Careful: dimension of the empty context should be -1
  dimC : Pre-Ctx → ℕ
  dimC nil = O
  dimC (Γ :: (x , A)) = max (dimC Γ) (dim A)


  {- Action of substitutions on types and terms on a syntactical level -}
  _[_]Pre-Ty : Pre-Ty → Pre-Sub → Pre-Ty
  _[_]Pre-Tm : Pre-Tm → Pre-Sub → Pre-Tm

  ∗ [ γ ]Pre-Ty = ∗
  ⇒ A t u [ γ ]Pre-Ty = ⇒ (A [ γ ]Pre-Ty) (t [ γ ]Pre-Tm) (u [ γ ]Pre-Tm)
  Var x [ nil ]Pre-Tm = Var x
  Var x [ γ :: (v , t) ]Pre-Tm = if x ≡ v then t else ((Var x) [ γ ]Pre-Tm)

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

  _∈_ : ℕ → Pre-Ctx → Set
  _ ∈ nil = ⊥
  x ∈ (Γ :: (y , _)) = (x ∈ Γ) + (x == y)

  eqdec-PreCtx : eqdec Pre-Ctx
  eqdec-PreTy : eqdec Pre-Ty
  eqdec-PreTm : eqdec Pre-Tm

  eqdec-PreCtx nil nil = inl idp
  eqdec-PreCtx nil (_ :: _) = inr λ()
  eqdec-PreCtx (_ :: _) nil = inr λ()
  eqdec-PreCtx (Γ :: (n , A)) (Δ :: (m , B)) with eqdec-PreCtx Γ Δ | eqdecℕ n m | eqdec-PreTy A B
  ... | inl idp | inl idp | inl idp = inl idp
  ... | inl idp | inl idp | inr A≠B = inr λ Γ,A=Γ,B → A≠B (snd (=, (snd (=:: Γ,A=Γ,B))))
  ... | inl idp | inr n≠m | _ = inr λ Γ,A=Γ,B → n≠m (fst (=, (snd (=:: Γ,A=Γ,B))))
  ... | inr Γ≠Δ | _ | _ = inr λ{idp → Γ≠Δ idp}

  eqdec-PreTy ∗ ∗ = inl idp
  eqdec-PreTy ∗ (⇒ _ _ _) = inr λ()
  eqdec-PreTy (⇒ _ _ _) ∗ = inr λ()
  eqdec-PreTy (⇒ A t u) (⇒ B v w) with eqdec-PreTy A B | eqdec-PreTm t v | eqdec-PreTm u w
  ... | inl idp | inl idp | inl idp = inl idp
  ... | inl idp | inl idp | inr u≠w = inr λ A=B → u≠w (snd (=⇒ A=B))
  ... | inl idp | inr t≠v | _ = inr λ A=B → t≠v (snd (fst (=⇒ A=B)))
  ... | inr A≠B | _ | _ = inr λ{idp → A≠B idp}

  eqdec-PreTm (Var a) (Var b) with eqdecℕ a b
  ... | inl idp = inl idp
  ... | inr a≠b = inr λ{idp → a≠b idp}
