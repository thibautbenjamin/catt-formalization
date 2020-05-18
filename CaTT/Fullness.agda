{-# OPTIONS --rewriting --allow-unsolved-metas #-}

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

  is-prop-full : ∀ Γ A → is-prop (A is-full-in Γ)
  is-prop-full = {!!}

  -- TODO : move this at the right place
  eqdec-ps : eqdec ps-ctx
  eqdec-ps = {!!}
  eqdec-Ty : eqdec Ty
  eqdec-Tm : eqdec Tm
  eqdec-Sub : eqdec Sub

  eqdec-Ty ∗ ∗ = inl idp
  eqdec-Ty ∗ (⇒ _ _ _) = inr λ{()}
  eqdec-Ty (⇒ _ _ _) ∗ = inr λ{()}
  eqdec-Ty (⇒ A t u) (⇒ A' t' u') with eqdec-Ty A A' | eqdec-Tm t t' | eqdec-Tm u u'
  ...                                        | inl idp | inl idp | inl idp = inl idp
  ...                                        | inr A≠A' | _ | _ = inr λ {idp → A≠A' idp}
  ...                                        | inl idp | inr t≠t' | _ = inr λ {idp → t≠t' idp}
  ...                                        | inl idp | inl idp | inr u≠u' = inr λ {idp → u≠u' idp}
  eqdec-Tm (v x) (v y) with eqdecℕ x y
  ...                   | inl idp = inl idp
  ...                   | inr x≠y = inr λ{idp → x≠y idp}
  eqdec-Tm (v _) (coh _ _ _ _) = inr λ{()}
  eqdec-Tm (coh _ _ _ _) (v _) = inr λ{()}
  eqdec-Tm (coh Γ A Afull γ) (coh Γ' A' A'full γ') with eqdec-ps Γ Γ' | eqdec-Ty A A' | eqdec-Sub γ γ'
  ...                                               | inl idp | inl idp | inl idp = inl (ap (λ X → coh Γ A X γ) (is-prop-has-all-paths (is-prop-full Γ A) Afull A'full))
  ...                                               | inr Γ≠Γ' | _ | _ = inr λ {idp → Γ≠Γ' idp}
  ...                                               | inl idp | inr A≠A' | _ = inr λ {idp → A≠A' idp}
  ...                                               | inl idp | inl idp | inr γ≠γ' = inr λ {idp → γ≠γ' idp}
  eqdec-Sub <> <> = inl idp
  eqdec-Sub <> < _ , _ ↦ _ > = inr λ{()}
  eqdec-Sub < _ , _ ↦ _ > <> = inr λ{()}
  eqdec-Sub < γ , x ↦ t > < γ' , x' ↦ t' > with eqdec-Sub γ γ' | eqdecℕ x x' | eqdec-Tm t t'
  ...                                        | inl idp | inl idp | inl idp = inl idp
  ...                                        | inr γ≠γ' | _ | _ = inr λ {idp → γ≠γ' idp}
  ...                                        | inl idp | inr x≠x' | _ = inr λ {idp → x≠x' idp}
  ...                                        | inl idp | inl idp | inr t≠t' = inr λ {idp → t≠t' idp}
