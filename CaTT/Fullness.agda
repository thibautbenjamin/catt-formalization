{-# OPTIONS --rewriting #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Disks
open import CaTT.Ps-contexts
open import Sets ℕ eqdecℕ

module CaTT.Fullness where

  data Ty : Set₁
  data Tm : Set₁
  data Sub : Set₁

  data _is-full-in_ : Ty → ps-ctx → Set₁


  data Ty where
    ∗ : Ty
    ⇒ : Ty → Tm → Tm → Ty
  data Tm where
    v : ℕ → Tm
    coh : (Γ : ps-ctx) → (A : Ty) → A is-full-in Γ → Sub  → Tm
  data Sub where
    <> : Sub
    <_,_↦_> : Sub → ℕ → Tm → Sub

  lvarT : Ty → list ℕ
  lvart : Tm → list ℕ
  lvarS : Sub → list ℕ

  lvarT ∗ = nil
  lvarT (⇒ A t u) = (lvarT A ++ lvart t) ++ lvart u
  lvart (v x) = nil :: x
  lvart (coh _ _ _ γ) = lvarS γ
  lvarS <> = nil
  lvarS < γ , _ ↦ t > = lvarS γ ++ lvart t

  varT : Ty → set
  varT A = set-of-list (lvarT A)

  vart : Tm → set
  vart t = set-of-list (lvart t)

  data _is-full-in_ where
    side-cond₁ : ∀ Γ A t u → (src-var _ (snd Γ)) == ((varT A) ∪-set (vart t)) → (tgt-var _ (snd Γ)) == ((varT A) ∪-set (vart u)) → (⇒ A t u) is-full-in Γ
    side-cond₂ : ∀ Γ A →  (varC (fst Γ)) == (varT A) → A is-full-in Γ

