{-# OPTIONS --rewriting --without-K #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax



{- Type theory for globular sets -}
module Globular-TT.Uniqueness-Derivations {l}
  (index : Set l) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index)) (eqdec-index : eqdec index)  where

  open import Globular-TT.Syntax index
  open import Globular-TT.Rules index rule
  open import Globular-TT.Eqdec-syntax index eqdec-index

  lΓ≤n→n∉Γ : ∀ {Γ A} n → Γ ⊢C → C-length Γ ≤ n →  ¬ (n # A ∈ Γ)
  lΓ≤n→n∉Γ n (cc Γ⊢ Γ⊢A idp) Sl≤n (inl x) = lΓ≤n→n∉Γ n Γ⊢ (≤T (n≤Sn _) Sl≤n) x
  lΓ≤n→n∉Γ n (cc Γ⊢ Γ⊢A idp) Sl≤n (inr (idp , idp)) = Sn≰n _ Sl≤n

  lΓ∉Γ : ∀ {Γ A} → Γ ⊢C → ¬ (C-length Γ # A ∈ Γ)
  lΓ∉Γ Γ⊢ = lΓ≤n→n∉Γ _ Γ⊢ (n≤n _)

  has-all-paths-∈ : ∀ {Γ x A} → Γ ⊢C → has-all-paths (x # A ∈ Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A idp) (inl x∈Γ) (inl x∈'Γ) = ap inl (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A idp) (inr (p , q)) (inr (p' , q')) = inr= (,= (is-prop-has-all-paths (eqdec-is-set eqdecℕ _ _) p p') (is-prop-has-all-paths (eqdec-is-set eqdec-Ty _ _) q q'))
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A idp) (inl x∈Γ) (inr (idp , idp)) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ ∙ y # B} {x} {A} (cc Γ⊢ γ⊢A idp) (inr (idp , idp)) (inl x∈Γ) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)

  has-all-paths-⊢C : ∀ {Γ} → has-all-paths (Γ ⊢C)
  has-all-paths-⊢T : ∀ {Γ A} → has-all-paths (Γ ⊢T A)
  has-all-paths-⊢t : ∀ {Γ A t} → has-all-paths (Γ ⊢t t # A)
  has-all-paths-⊢S : ∀ {Δ Γ γ} → has-all-paths (Δ ⊢S γ > Γ)

  has-all-paths-⊢C {⊘} ec ec = idp
  has-all-paths-⊢C {Γ ∙ x # A} (cc Γ⊢ Γ⊢A p) (cc Γ⊢' Γ⊢'A q) = ap³ cc (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-⊢T Γ⊢A Γ⊢'A) (is-prop-has-all-paths (eqdec-is-set (eqdecℕ) _ _) p q)

  has-all-paths-⊢T {Γ} {∗} (ob Γ⊢) (ob Γ⊢') = ap ob (has-all-paths-⊢C Γ⊢ Γ⊢')
  has-all-paths-⊢T {Γ} {⇒ A t u} (ar Γ⊢A Γ⊢t:A Γ⊢u:A) (ar Γ⊢'A Γ⊢'t:A Γ⊢'u:A) = ap³ ar (has-all-paths-⊢T Γ⊢A Γ⊢'A) (has-all-paths-⊢t Γ⊢t:A Γ⊢'t:A) (has-all-paths-⊢t Γ⊢u:A Γ⊢'u:A)

  has-all-paths-⊢t {Γ} {A} {Var x} (var Γ⊢ x∈Γ) (var Γ⊢' x∈'Γ) = ap² var (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  has-all-paths-⊢t {Γ} {A} {Tm-constructor i γ} (tm Ci⊢Ti Γ⊢γ p) (tm Ci⊢'Ti Γ⊢'γ p') = ap³ tm (has-all-paths-⊢T Ci⊢Ti Ci⊢'Ti) (has-all-paths-⊢S Γ⊢γ Γ⊢'γ) (is-prop-has-all-paths (eqdec-is-set eqdec-Ty _ _) p p')

  has-all-paths-⊢S {Δ} {Γ} {<>} (es Δ⊢) (es Δ⊢')= ap es (has-all-paths-⊢C Δ⊢ Δ⊢')
  has-all-paths-⊢S {Δ} {Γ} {< γ , x ↦ t >} (sc Δ⊢γ Γ+⊢ Δ⊢t p) (sc Δ⊢'γ Γ+⊢' Δ⊢'t q) = ap⁴ sc (has-all-paths-⊢S Δ⊢γ Δ⊢'γ) (has-all-paths-⊢C Γ+⊢ Γ+⊢') (has-all-paths-⊢t Δ⊢t Δ⊢'t) (is-prop-has-all-paths (eqdec-is-set (eqdecℕ) _ _) p q)

  is-prop-⊢C : ∀ Γ → is-prop (Γ ⊢C)
  is-prop-⊢T : ∀ Γ A → is-prop (Γ ⊢T A)
  is-prop-⊢t : ∀ Γ A t → is-prop (Γ ⊢t t # A)
  is-prop-⊢S : ∀ Δ Γ γ → is-prop (Δ ⊢S γ > Γ)

  is-prop-⊢C Γ = has-all-paths-is-prop has-all-paths-⊢C
  is-prop-⊢T Γ A = has-all-paths-is-prop has-all-paths-⊢T
  is-prop-⊢t Γ A t = has-all-paths-is-prop has-all-paths-⊢t
  is-prop-⊢S Γ Δ γ = has-all-paths-is-prop has-all-paths-⊢S

  unique-type : ∀ {Γ t u A B} → (Γ ⊢t t # A) → (Γ ⊢t u # B) →  t == u → A == B
  unique-type (var (cc Γ⊢ _ idp) (inl a)) (var _ (inl b)) idp = unique-type (var Γ⊢ a) (var Γ⊢ b) idp
  unique-type (var (cc Γ⊢ _ idp) (inr (idp , _))) (var _ (inl l∈Γ)) idp = ⊥-elim (lΓ∉Γ Γ⊢ l∈Γ)
  unique-type (var (cc Γ⊢ _ idp) (inl l∈Γ)) (var _ (inr (idp , _))) idp = ⊥-elim (lΓ∉Γ Γ⊢ l∈Γ)
  unique-type (var (cc Γ⊢ _ idp) (inr (idp , idp))) (var _ (inr (idp , idp))) _ = idp
  unique-type (tm _ _ p) (tm _ _ q) idp = p >> (q ^)
