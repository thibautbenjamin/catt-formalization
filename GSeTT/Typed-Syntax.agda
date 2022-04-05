{-# OPTIONS --without-K #-}

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

  eqC : ∀ (Γ Δ : Ctx) → fst Γ == fst Δ → Γ == Δ
  eqC (Γ , Γ⊢) (.Γ , Γ⊢') idp = Σ= idp (has-all-paths-⊢C _ _)

  eqT : ∀ {Γ} (A B : Ty Γ) → fst A == fst B → A == B
  eqT (A , Γ⊢A) (.A , Γ⊢'A) idp = Σ= idp (has-all-paths-⊢T _ _)

  eqt : ∀ {Γ A} (t u : Tm Γ A) → fst t == fst u → t == u
  eqt (t , Γ⊢t:A) (.t , Γ⊢':A) idp = Σ= idp (has-all-paths-⊢t _ _)

  eqS : ∀ {Γ Δ} (γ δ : Sub Γ Δ) → fst γ == fst δ → γ == δ
  eqS (γ , Γ⊢γ:Δ) (.γ , Γ⊢'γ:Δ) idp = Σ= idp (has-all-paths-⊢S _ _)

  trS : ∀ {Γ Δ Θ : Ctx} → (p : Δ == Θ) → {γ : Sub Γ Δ} → {δ : Sub Γ Θ} → fst γ == fst δ → transport p γ == δ
  trS {Γ} {Δ} {Θ} idp {γ} {δ} x = eqS {Γ} {Θ} γ δ x

  eqdec-Ty : ∀ Γ → eqdec (Ty Γ)
  eqdec-Ty Γ (A , Γ⊢A) (B , Γ⊢B) with eqdec-PreTy A B
  ... | inl idp = inl (eqT {Γ} (A , Γ⊢A) (B , Γ⊢B) idp)
  ... | inr A≠B = inr λ p → A≠B (fst-is-inj p)

  is-set-Ty : ∀ Γ → is-set (Ty Γ)
  is-set-Ty Γ = eqdec-is-set (eqdec-Ty Γ)
