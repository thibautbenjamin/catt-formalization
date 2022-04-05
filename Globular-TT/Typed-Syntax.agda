{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax



{- Type theory for globular sets -}
module Globular-TT.Typed-Syntax {l}
  (index : Set l) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index)) (eqdec-index : eqdec index)  where

  open import Globular-TT.Syntax index
  open import Globular-TT.Rules index rule
  open import Globular-TT.Eqdec-syntax index eqdec-index
  open import Globular-TT.Uniqueness-Derivations index rule eqdec-index

  Ctx : Set (lsuc l)
  Ctx = Σ Pre-Ctx (λ Γ → Γ ⊢C)

  Ty : Ctx → Set (lsuc l)
  Ty (Γ , _) = Σ Pre-Ty (λ A → Γ ⊢T A)

  Tm : ∀ (Γ : Ctx) → Ty Γ → Set (lsuc l)
  Tm (Γ , _) (A , _) = Σ Pre-Tm (λ t → Γ ⊢t t # A)

  Sub : ∀ (Δ : Ctx) (Γ : Ctx) → Set (lsuc l)
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

  private
    eqdec-typedTy : ∀ Γ → eqdec (Ty Γ)
    eqdec-typedTy Γ (A , Γ⊢A) (B , Γ⊢B) with eqdec-Ty A B
    ... | inl idp = inl (eqT {Γ} (A , Γ⊢A) (B , Γ⊢B) idp)
    ... | inr A≠B = inr λ p → A≠B (fst-is-inj p)

  is-set-Ty : ∀ Γ → is-set (Ty Γ)
  is-set-Ty Γ = eqdec-is-set (eqdec-typedTy Γ)
