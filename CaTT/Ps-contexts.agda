{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Disks
open import Sets ℕ eqdecℕ

{- PS-contexts -}
module CaTT.Ps-contexts where

  {- Rules for PS-contexts -}
  data _⊢ps_#_ : Pre-Ctx → ℕ → Pre-Ty → Set where
    pss : (nil :: (O , ∗)) ⊢ps O # ∗
    psd : ∀ {Γ f A x y} → Γ ⊢ps f # (⇒ A (Var x) (Var y)) → Γ ⊢ps y # A
    pse : ∀ {Γ x A} → Γ ⊢ps x # A → ((Γ :: ((length Γ) , A)) :: (S (length Γ) , ⇒ A (Var x) (Var (length Γ)))) ⊢ps S (length Γ) # ⇒ A (Var x) (Var (length Γ))

  data _⊢ps : Pre-Ctx → Set where
    ps : ∀ {Γ x} → Γ ⊢ps x # ∗ → Γ ⊢ps


  {- PS-contexts define valid contexts -}
  Γ⊢ps→Γ⊢ : ∀ {Γ} → Γ ⊢ps → Γ ⊢C
  Γ⊢psx:A→Γ⊢x:A : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢t (Var x) # A

  Γ⊢ps→Γ⊢ (ps Γ⊢psx) = Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx)
  Γ⊢psx:A→Γ⊢x:A pss = var (cc ec (ob ec)) (inr (idp , idp))
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) with Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psf:x⇒y)
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) | ar _ Γ⊢y:A = Γ⊢y:A
  Γ⊢psx:A→Γ⊢x:A (pse Γ⊢psx:A) with (cc (Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)) (Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)))
  ...                          | Γ,y:A⊢ = var (cc Γ,y:A⊢ (ar (wkt (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A) Γ,y:A⊢) (var Γ,y:A⊢ (inr (idp , idp))))) (inr (idp , idp))

  ps-ctx : Set₁
  ps-ctx = Σ Pre-Ctx (λ Γ → Γ ⊢ps)

  {- Eric's trick : is a src-var -}
  varC : Pre-Ctx → set
  varC nil = Ø
  varC (Γ :: (x , _)) = add+ (varC Γ) (nil :: x)

  src-var : ∀ Γ → Γ ⊢ps → set
  src-var Γ (ps Γ⊢psx) = {!srcᵢ-var (dim Γ) Γ⊢psx!}

  tgt-var : ∀ Γ → Γ ⊢ps → set
  tgt-var = {!!}

