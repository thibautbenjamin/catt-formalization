{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules

{- Type theory for globular sets -}
module GSeTT.Uniqueness-Derivations where

  has-all-paths-∈ : ∀ {Γ x A} → Γ ⊢C → has-all-paths (x # A ∈ Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A idp) (inl x∈Γ) (inl x∈'Γ) = ap inl (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A idp) (inl x∈Γ) (inr (idp , idp)) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A idp) (inr (idp , idp)) (inl x∈Γ) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  has-all-paths-∈ {Γ :: (y , B)} {x} {A} (cc Γ⊢ γ⊢A idp) (inr (idp , idp)) (inr (p' , q')) =
    ap inr (,= (is-prop-has-all-paths (is-setℕ x (length Γ)) idp p') (is-prop-has-all-paths ((eqdec-is-set eqdec-PreTy) A B) idp q'))

  has-all-paths-⊢C : ∀ {Γ} → has-all-paths (Γ ⊢C)
  has-all-paths-⊢T : ∀ {Γ A} → has-all-paths (Γ ⊢T A)
  has-all-paths-⊢t : ∀ {Γ A t} → has-all-paths (Γ ⊢t t # A)
  has-all-paths-⊢S : ∀ {Δ Γ γ} → has-all-paths (Δ ⊢S γ > Γ)

  has-all-paths-⊢C {nil} ec ec = idp
  has-all-paths-⊢C {Γ :: (x , A)} (cc Γ⊢ Γ⊢A p) (cc Γ⊢' Γ⊢'A q) = ap³ cc ((has-all-paths-⊢C Γ⊢ Γ⊢')) ((has-all-paths-⊢T Γ⊢A Γ⊢'A)) (is-prop-has-all-paths (is-setℕ x (length Γ)) p q)

  has-all-paths-⊢T {Γ} {∗} (ob Γ⊢) (ob Γ⊢') = ap ob (has-all-paths-⊢C Γ⊢ Γ⊢')
  has-all-paths-⊢T {Γ} {⇒ A t u} (ar Γ⊢t:A Γ⊢u:A) (ar Γ⊢'t:A Γ⊢'u:A) = ap² ar (has-all-paths-⊢t Γ⊢t:A Γ⊢'t:A) (has-all-paths-⊢t Γ⊢u:A Γ⊢'u:A)

  has-all-paths-⊢t {Γ} {A} {Var x} (var Γ⊢ x∈Γ) (var Γ⊢' x∈'Γ) = ap² var (has-all-paths-⊢C Γ⊢ Γ⊢') (has-all-paths-∈ Γ⊢ x∈Γ x∈'Γ)

  has-all-paths-⊢S {Δ} {Γ} {<>} (es Δ⊢) (es Δ⊢')= ap es (has-all-paths-⊢C Δ⊢ Δ⊢')
  has-all-paths-⊢S {Δ} {Γ :: (y , A)} {γ :: (x , t)} (sc Δ⊢γ Γ+⊢ Δ⊢t p) (sc Δ⊢'γ Γ+⊢' Δ⊢'t q) =
    ap⁴ sc (has-all-paths-⊢S Δ⊢γ Δ⊢'γ) (has-all-paths-⊢C Γ+⊢ Γ+⊢') (has-all-paths-⊢t Δ⊢t Δ⊢'t) (is-prop-has-all-paths (is-setℕ y x) p q)

  is-prop-⊢C : ∀ Γ → is-prop (Γ ⊢C)
  is-prop-⊢T : ∀ Γ A → is-prop (Γ ⊢T A)
  is-prop-⊢t : ∀ Γ A t → is-prop (Γ ⊢t t # A)
  is-prop-⊢S : ∀ Δ Γ γ → is-prop (Δ ⊢S γ > Γ)

  is-prop-⊢C Γ = has-all-paths-is-prop has-all-paths-⊢C
  is-prop-⊢T Γ A = has-all-paths-is-prop has-all-paths-⊢T
  is-prop-⊢t Γ A t = has-all-paths-is-prop has-all-paths-⊢t
  is-prop-⊢S Γ Δ γ = has-all-paths-is-prop has-all-paths-⊢S


  Γ⊢→length∉ : ∀ {Γ A n} → length Γ ≤ n → Γ ⊢C → ¬ (n # A ∈ Γ)
  Γ⊢→length∉ {.(_ :: (length _ , _))} Sl≤n (cc Γ⊢ x₁ idp) (inl n∈Γ) = Γ⊢→length∉ (Sn≤m→n≤m Sl≤n) Γ⊢ n∈Γ
  Γ⊢→length∉ {.(_ :: (length _ , _))} Sl≤l (cc Γ⊢ x₁ idp) (inr (idp , idp)) = Sn≰n _ Sl≤l

  unique-type : ∀ {Γ t u A B} → (Γ ⊢t t # A) → (Γ ⊢t u # B) →  t == u → A == B
  unique-type {Γ :: a} (var _ (inr (idp , idp))) (var _ (inr (idp , idp))) _ = idp
  unique-type {Γ :: .(_ , _)} (var x (inl x∈Γ)) (var (cc Γ⊢ _ p) (inl x'∈Γ)) idp = unique-type (var Γ⊢ x∈Γ) (var Γ⊢ x'∈Γ ) idp
  unique-type {Γ :: .(_ , _)} (var _ (inl x∈Γ)) (var (cc Γ⊢ _ idp) (inr (idp , idp))) idp = ⊥-elim (Γ⊢→length∉ (n≤n _) Γ⊢ x∈Γ)
  unique-type {Γ :: .(_ , _)} (var (cc Γ⊢ _ idp) (inr (idp , idp))) (var _ (inl x∈Γ)) idp = ⊥-elim (Γ⊢→length∉ (n≤n _) Γ⊢ x∈Γ)
