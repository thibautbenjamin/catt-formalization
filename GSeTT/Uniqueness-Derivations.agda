{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules

{- Type theory for globular sets -}
module GSeTT.Uniqueness-Derivations where
  ap² : ∀ {i j k} {A : Set i} {B : Set k} {C : Set j} {a a' : A} {b b' : B} (f : A → B → C) → a == a' →  b == b' → (f a b) == (f a' b')
  ap² f idp idp = idp

  ap³ : ∀ {i j k l} {A : Set i} {B : Set k} {C : Set j} {D : Set l} {a a' : A} {b b' : B} {c c' : C} (f : A → B → C → D) → a == a' →  b == b' → c == c' → (f a b c) == (f a' b' c')
  ap³ f idp idp idp = idp


  has-all-paths-∈ : ∀ {Γ x A} → Γ ⊢C → has-all-paths (x # A ∈ Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A) (inl x∈Γ) (inl x∈'Γ) = ap inl (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A) (inl x∈Γ) (inr (idp , idp)) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A) (inr (idp , idp)) (inl x∈Γ) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A) (inr (idp , idp)) (inr (idp , idp)) = idp

  has-all-paths-⊢C : ∀ {Γ} → has-all-paths (Γ ⊢C)
  has-all-paths-⊢T : ∀ {Γ A} → has-all-paths (Γ ⊢T A)
  has-all-paths-⊢t : ∀ {Γ A t} → has-all-paths (Γ ⊢t t # A)
  has-all-paths-⊢S : ∀ {Δ Γ γ} → has-all-paths (Δ ⊢S γ > Γ)

  has-all-paths-⊢C {⊘} ec ec = idp
  has-all-paths-⊢C {Γ :: (x , A)} (cc Γ⊢ Γ⊢A) (cc Γ⊢' Γ⊢'A) = ap² cc (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-⊢T Γ⊢A Γ⊢'A)

  has-all-paths-⊢T {Γ} {∗} (ob Γ⊢) (ob Γ⊢') = ap ob (has-all-paths-⊢C Γ⊢ Γ⊢')
  has-all-paths-⊢T {Γ} {⇒ A t u} (ar Γ⊢t:A Γ⊢u:A) (ar Γ⊢'t:A Γ⊢'u:A) = ap² ar (has-all-paths-⊢t Γ⊢t:A Γ⊢'t:A) (has-all-paths-⊢t Γ⊢u:A Γ⊢'u:A)

  has-all-paths-⊢t {Γ} {A} {Var x} (var Γ⊢ x∈Γ) (var Γ⊢' x∈'Γ) = ap² var (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  -- has-all-paths-⊢t {Γ} {A} {Tm-constructor i γ} (tm i Ci⊢Ti Γ⊢γ) (tm i Ci⊢'Ti Γ⊢'γ)= ap² (tm i) (has-all-paths-⊢T Ci⊢Ti Ci⊢'Ti) (has-all-paths-⊢S Γ⊢γ Γ⊢'γ)

  has-all-paths-⊢S {Δ} {Γ} {<>} (es Δ⊢) (es Δ⊢')= ap es (has-all-paths-⊢C Δ⊢ Δ⊢')
  has-all-paths-⊢S {Δ} {Γ} {γ :: (x , t)} (sc Δ⊢γ Γ+⊢ Δ⊢t) (sc Δ⊢'γ Γ+⊢' Δ⊢'t) = ap³ sc (has-all-paths-⊢S Δ⊢γ Δ⊢'γ) (has-all-paths-⊢C Γ+⊢ Γ+⊢') (has-all-paths-⊢t Δ⊢t Δ⊢'t)

  is-prop-⊢C : ∀ Γ → is-prop (Γ ⊢C)
  is-prop-⊢T : ∀ Γ A → is-prop (Γ ⊢T A)
  is-prop-⊢t : ∀ Γ A t → is-prop (Γ ⊢t t # A)
  is-prop-⊢S : ∀ Δ Γ γ → is-prop (Δ ⊢S γ > Γ)

  is-prop-⊢C Γ = has-all-paths-is-prop has-all-paths-⊢C
  is-prop-⊢T Γ A = has-all-paths-is-prop has-all-paths-⊢T
  is-prop-⊢t Γ A t = has-all-paths-is-prop has-all-paths-⊢t
  is-prop-⊢S Γ Δ γ = has-all-paths-is-prop has-all-paths-⊢S


