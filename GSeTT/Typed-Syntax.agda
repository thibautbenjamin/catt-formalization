{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.CwF-structure
open import GSeTT.Uniqueness-Derivations

{- Typed syntax for type theory for globular sets -}
module GSeTT.Typed-Syntax where
  Ctx : Set₁
  Ctx = Σ Pre-Ctx (λ Γ → Γ ⊢C)

  Ty : Ctx → Set₁
  Ty (Γ , _) = Σ Pre-Ty (λ A → Γ ⊢T A)

  Tm : ∀ (Γ : Ctx) → Ty Γ → Set₁
  Tm (Γ , _) (A , _) = Σ Pre-Tm (λ t → Γ ⊢t t # A)

  Sub : ∀ (Δ : Ctx) (Γ : Ctx) → Set₁
  Sub (Δ , _) (Γ , _) = Σ Pre-Sub (λ γ → Δ ⊢S γ > Γ)

 {- Operations of typed syntax -}
  _∙_ : ∀ (Γ : Ctx) → Ty Γ → Ctx
  (Γ , Γ⊢) ∙ (A , Γ⊢A) = (Γ :: ((length Γ) , A )) , cc Γ⊢ Γ⊢A

 -- TODO : define all operation on typed syntax and check Dybjer's axioms



