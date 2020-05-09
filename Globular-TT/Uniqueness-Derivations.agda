{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax



{- Type theory for globular sets -}
module Globular-TT.Uniqueness-Derivations
  (index : Set) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index))
  (assumption : ∀ i → (Globular-TT.Syntax.dimC index) ((Globular-TT.Syntax.GPre-Ctx index) (fst (fst (rule i)))) ≤ (Globular-TT.Syntax.dim index) (snd (rule i)))
  (eqdec-index : eqdec index) where

  open import Globular-TT.Syntax index
  open import Globular-TT.Rules index rule

  ap² : ∀ {i j k} {A : Set i} {B : Set k} {C : Set j} {a a' : A} {b b' : B} (f : A → B → C) → a == a' →  b == b' → (f a b) == (f a' b')
  ap² f idp idp = idp

  ap³ : ∀ {i j k l} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {a a' : A} {b b' : B} {c c' : C} (f : A → B → C → D) → a == a' →  b == b' → c == c' → (f a b c) == (f a' b' c')
  ap³ f idp idp idp = idp

  lΓ≤n→n∉Γ : ∀ {Γ A} n → Γ ⊢C → C-length Γ ≤ n →  ¬ (n # A ∈ Γ)
  lΓ≤n→n∉Γ n (cc Γ⊢ Γ⊢A) Sl≤n (inl x) = lΓ≤n→n∉Γ n Γ⊢ (≤T (n≤Sn _) Sl≤n) x
  lΓ≤n→n∉Γ n (cc Γ⊢ Γ⊢A) Sl≤n (inr (idp , idp)) = Sn≰n _ Sl≤n


  lΓ∉Γ : ∀ {Γ A} → Γ ⊢C → ¬ (C-length Γ # A ∈ Γ)
  lΓ∉Γ Γ⊢ = lΓ≤n→n∉Γ _ Γ⊢ (n≤n _)

  has-all-paths-∈ : ∀ {Γ x A} → Γ ⊢C → has-all-paths (x # A ∈ Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A) (inl x∈Γ) (inl x∈'Γ) = ap inl (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A) (inl x∈Γ) (inr (idp , idp)) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A) (inr (idp , idp)) (inl x∈Γ) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A) (inr (idp , idp)) (inr (idp , idp)) = idp

  has-all-paths-⊢C : ∀ {Γ} → has-all-paths (Γ ⊢C)
  has-all-paths-⊢T : ∀ {Γ A} → has-all-paths (Γ ⊢T A)
  has-all-paths-⊢t : ∀ {Γ A t} → has-all-paths (Γ ⊢t t # A)
  has-all-paths-⊢S : ∀ {Δ Γ γ} → has-all-paths (Δ ⊢S γ > Γ)

  has-all-paths-⊢C {⊘} ec ec = idp
  has-all-paths-⊢C {Γ ∙ x # A} (cc Γ⊢ Γ⊢A) (cc Γ⊢' Γ⊢'A) = ap² cc (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-⊢T Γ⊢A Γ⊢'A)

  has-all-paths-⊢T {Γ} {∗} (ob Γ⊢) (ob Γ⊢') = ap ob (has-all-paths-⊢C Γ⊢ Γ⊢')
  has-all-paths-⊢T {Γ} {⇒ A t u} (ar Γ⊢A Γ⊢t:A Γ⊢u:A) (ar Γ⊢'A Γ⊢'t:A Γ⊢'u:A) = ap³ ar (has-all-paths-⊢T Γ⊢A Γ⊢'A) (has-all-paths-⊢t Γ⊢t:A Γ⊢'t:A) (has-all-paths-⊢t Γ⊢u:A Γ⊢'u:A)

  has-all-paths-⊢t {Γ} {A} {Var x} (var Γ⊢ x∈Γ) (var Γ⊢' x∈'Γ) = ap² var (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  has-all-paths-⊢t {Γ} {A} {Tm-constructor i γ} (tm i Ci⊢Ti Γ⊢γ) (tm i Ci⊢'Ti Γ⊢'γ)= ap² (tm i) (has-all-paths-⊢T Ci⊢Ti Ci⊢'Ti) (has-all-paths-⊢S Γ⊢γ Γ⊢'γ)

  has-all-paths-⊢S {Δ} {Γ} {<>} (es Δ⊢) (es Δ⊢')= ap es (has-all-paths-⊢C Δ⊢ Δ⊢')
  has-all-paths-⊢S {Δ} {Γ} {< γ , x ↦ t >} (sc Δ⊢γ Γ+⊢ Δ⊢t) (sc Δ⊢'γ Γ+⊢' Δ⊢'t) = ap³ sc (has-all-paths-⊢S Δ⊢γ Δ⊢'γ) (has-all-paths-⊢C Γ+⊢ Γ+⊢') (has-all-paths-⊢t Δ⊢t Δ⊢'t)

  is-contr-⊢C : ∀ Γ → is-contr (Γ ⊢C)
  is-contr-⊢T : ∀ Γ A → is-contr (Γ ⊢T A)
  is-contr-⊢t : ∀ Γ A t → is-contr (Γ ⊢t t # A)
  is-contr-⊢S : ∀ Δ Γ γ → is-contr (Δ ⊢S γ > Γ)

