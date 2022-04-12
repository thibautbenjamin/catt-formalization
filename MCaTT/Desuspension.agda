{-# OPTIONS --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Uniqueness-Derivations
open import CaTT.Fullness
open import CaTT.CaTT


module MCaTT.Desuspension where

  ↓C : ∀ (Γ : Pre-Ctx) → Γ ⊢C → Pre-Ctx
  ↓T : ∀ (Γ : Pre-Ctx) (A : Pre-Ty) → Γ ⊢T A → Pre-Ty
  ↓t : ∀ (Γ : Pre-Ctx) (A : Pre-Ty) (x : ℕ) → Γ ⊢t (Var x) # A → ℕ
  count-points : ∀ (Γ : Pre-Ctx) → ℕ

  ↓C nil _ = nil
  ↓C (Γ :: (x , ∗)) (cc Γ⊢ _ _) = ↓C Γ Γ⊢
  ↓C Γ+@(Γ :: (x , A@(⇒ _ _ _))) Γ+⊢@(cc Γ⊢ Γ⊢A _) = ↓C Γ Γ⊢ :: (↓t Γ+ A x (var Γ+⊢ (inr (idp , idp))) , ↓T Γ A Γ⊢A)

  ↓T Γ ∗ Γ⊢∗ = ∗
  ↓T Γ (⇒ ∗ _ _) _ = ∗
  ↓T Γ (⇒ A@(⇒ _ _ _) (Var x) (Var y)) (ar Γ⊢A Γ⊢x Γ⊢y) = ⇒ (↓T Γ A Γ⊢A) (Var (↓t Γ A x Γ⊢x)) (Var (↓t Γ A y Γ⊢y))

  count-points nil = 0
  count-points (Γ :: (x , ∗)) = S (count-points Γ)
  count-points (Γ :: (x , ⇒ _ _ _)) = count-points Γ

-- goes to Prelude
  _-_ : ℕ → ℕ → ℕ
  n - O = n
  O - S m = O
  S n - S m = n - m

  Sn-m : ∀ (n m : ℕ) → m ≤ n → (S n - m) == S (n - m)
  Sn-m n O _ = idp
  Sn-m O (S m) Sm≤0 = ⊥-elim (Sn≰0 _ Sm≤0)
  Sn-m (S n) (S m) (S≤ m≤n) = Sn-m n m m≤n
-- end of Prelude partA x₁ x₂

  ↓t (Γ :: (y , B)) A x (var _ (inr (_ , _))) = x - (count-points Γ)
  ↓t (Γ :: (y , B)) A x (var (cc Γ⊢ _ _) (inl x∈Γ)) = ↓t Γ A x (var Γ⊢ x∈Γ)

  count-points≤length : ∀ (Γ : Pre-Ctx) → count-points Γ ≤ length Γ
  count-points≤length nil = 0≤ 0
  count-points≤length (Γ :: (_ , ∗)) = S≤ (count-points≤length Γ)
  count-points≤length (Γ :: (_ , ⇒ _ _ _)) = n≤m→n≤Sm (count-points≤length Γ)

  ↓length : ∀ (Γ : Pre-Ctx) (Γ⊢ : Γ ⊢C) → (length Γ - count-points Γ) == length (↓C Γ Γ⊢)
  ↓length nil _ = idp
  ↓length (Γ :: (_ , ∗)) (cc Γ⊢ _ _) = ↓length Γ Γ⊢
  ↓length (Γ :: (x , ⇒ _ _ _)) (cc Γ⊢ _ _) = Sn-m (length Γ) (count-points Γ) (count-points≤length Γ) >> ap S (↓length Γ Γ⊢)

  wk↓T : ∀ (Γ : Pre-Ctx) (B : Pre-Ty) (y : ℕ) (A : Pre-Ty) (Γ⊢A : Γ ⊢T A) (Γ+⊢A : (Γ :: (y , B)) ⊢T A) → ↓T Γ A Γ⊢A == ↓T (Γ :: (y , B)) A Γ+⊢A
  wk↓t : ∀ (Γ : Pre-Ctx) (B : Pre-Ty) (y : ℕ) (x : ℕ) (A : Pre-Ty) (Γ⊢x : Γ ⊢t (Var x) # A) (Γ+⊢x : (Γ :: (y , B)) ⊢t (Var x) # A) → ↓t Γ A x Γ⊢x == ↓t (Γ :: (y , B)) A x Γ+⊢x

  wk↓T Γ B y ∗ Γ⊢A Γ+⊢A = idp
  wk↓T Γ B y (⇒ ∗ _ _) _ _ = idp
  wk↓T Γ B y (⇒ A@(⇒ _ _ _) (Var x) (Var x')) (ar Γ⊢A Γ⊢x Γ⊢x') (ar Γ+⊢A Γ+⊢x Γ+⊢x') = ⇒= (wk↓T Γ B y A Γ⊢A Γ+⊢A) (Var= (wk↓t Γ B y x A Γ⊢x Γ+⊢x)) (Var= (wk↓t Γ B y x' A Γ⊢x' Γ+⊢x'))

  wk↓t (Γ :: (z , C)) B y x A (var (cc Γ⊢ _ _) (inl x∈Γ)) (var (cc Γ+⊢ _ _) (inl (inl x∈Γ+))) = wk↓t Γ C z x A (var Γ⊢ x∈Γ) (var Γ+⊢ (inl (x∈Γ+)))
  wk↓t (Γ :: (.(length Γ) , C)) B .(length (Γ :: (length Γ , C))) .(length Γ) .C (var (cc Γ⊢ _ idp) (inl x∈Γ)) (var (cc _ _ idp) (inl (inr (idp , idp)))) = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  wk↓t (Γ :: (z , C)) B .(length (Γ :: (z , C))) .(length (Γ :: (z , C))) .B (var (cc Γ⊢ _ _) (inl x∈Γ)) (var (cc _ _ idp) (inr (idp , idp))) = ⊥-elim (n∉Γ Γ⊢ (n≤Sn _) x∈Γ)
  wk↓t (Γ :: (.(length Γ) , C)) B .(length (Γ :: (length Γ , C))) .(length Γ) .C (var (cc Γ⊢ _ idp) (inr (idp , idp))) (var (cc _ _ idp) (inl (inl lΓ∈Γ))) = ⊥-elim (lΓ∉Γ Γ⊢ lΓ∈Γ)
  wk↓t (Γ :: (.(length Γ) , C)) B .(length (Γ :: (length Γ , C))) .(length Γ) .C (var (cc Γ⊢ _ idp) (inr (idp , idp))) (var (cc _ _ idp) (inl (inr _))) = idp
  wk↓t (Γ :: (.(length Γ) , C)) B .(length (Γ :: (length Γ , C))) .(length Γ) .C (var (cc Γ⊢ _ idp) (inr (idp , idp))) (var (cc Γ+⊢ _ idp) (inr (contra , _))) = ⊥-elim (n≠Sn _ contra)

  ↓⊢C : ∀ (Γ : Pre-Ctx) (Γ⊢ : Γ ⊢C) → (↓C Γ Γ⊢) ⊢C
  ↓⊢T : ∀ (Γ : Pre-Ctx) (A : Pre-Ty) (A≠∗ : A ≠ ∗) (Γ⊢ : Γ ⊢C) (Γ⊢A : Γ ⊢T A) → (↓C Γ Γ⊢) ⊢T (↓T Γ A Γ⊢A)
  ↓⊢t : ∀ (Γ : Pre-Ctx) (A : Pre-Ty) (x : ℕ) (A≠∗ : A ≠ ∗) (Γ⊢ : Γ ⊢C) (Γ⊢A : Γ ⊢T A) (Γ⊢x : Γ ⊢t (Var x) # A) → (↓C Γ Γ⊢) ⊢t Var (↓t Γ A x Γ⊢x) # (↓T Γ A Γ⊢A)

  ↓wkt : ∀ (Γ : Pre-Ctx) (C : Pre-Ty) (y : ℕ) {A B : Pre-Ty} {t u : Pre-Tm} (Γ⊢ : Γ ⊢C) (Γ+⊢ : (Γ :: (y , C)) ⊢C) (↓Γ⊢t : ↓C Γ Γ⊢ ⊢t t # A) → A == B → t == u → ↓C (Γ :: (y , C)) Γ+⊢ ⊢t u # B
  ↓wkt Γ ∗ y {A = A} {t = t} Γ⊢ (cc Γ⊢' _ _) ↓Γ⊢t idp idp = transport {B = λ p → ↓C Γ p ⊢t t # A} (has-all-paths-⊢C Γ⊢ Γ⊢') ↓Γ⊢t
  ↓wkt Γ (⇒ C x x₁) y {A = A} {t = t} Γ⊢ Γ+⊢@(cc Γ⊢' _ _) ↓Γ⊢t idp idp = wkt (transport {B = λ p → ↓C Γ p ⊢t t # A} (has-all-paths-⊢C Γ⊢ Γ⊢') ↓Γ⊢t) (↓⊢C _ Γ+⊢)

  ↓⊢C nil ec = ec
  ↓⊢C (Γ :: (x , ∗)) (cc Γ⊢ _ _) = ↓⊢C Γ Γ⊢
  ↓⊢C (Γ :: (x , A@(⇒ B t u))) (cc Γ⊢ Γ⊢A idp) = cc (↓⊢C Γ Γ⊢) (↓⊢T Γ A (λ{()}) Γ⊢ Γ⊢A)  (↓length Γ Γ⊢)

  ↓⊢T Γ ∗ A≠∗ Γ⊢A = ⊥-elim (A≠∗ idp)
  ↓⊢T Γ (⇒ ∗ x _) A≠∗ Γ⊢ (ar Γ⊢A _ _) = ob (↓⊢C Γ Γ⊢)
  ↓⊢T Γ (⇒ A@(⇒ _ _ _) (Var x) (Var y)) A≠∗ Γ⊢ (ar Γ⊢A Γ⊢x Γ⊢y) = ar (↓⊢T Γ A (λ{()}) Γ⊢ Γ⊢A) (↓⊢t Γ A x (λ{()}) Γ⊢ Γ⊢A Γ⊢x) (↓⊢t Γ A y (λ{()}) Γ⊢ Γ⊢A Γ⊢y)

  ↓⊢t (Γ :: (y , B)) A x A≠∗ Γ+⊢@(cc Γ⊢ x₁ x₂) Γ+⊢A Γ+⊢x@(var _ (inl x∈Γ)) =
    let Γ⊢x = var Γ⊢ x∈Γ in
    let Γ⊢A = Γ⊢t:A→Γ⊢A Γ⊢x in
    ↓wkt Γ B y Γ⊢ Γ+⊢ (↓⊢t Γ A x A≠∗ Γ⊢ Γ⊢A Γ⊢x) (wk↓T Γ B y A Γ⊢A Γ+⊢A) (Var= (wk↓t Γ B y x A Γ⊢x Γ+⊢x))
  ↓⊢t Γ+@(Γ :: (x , ∗)) .∗ .x A≠∗ Γ+⊢@(cc _ _ _) Γ⊢A (var _ (inr (idp , idp))) = ⊥-elim (A≠∗ idp)
  ↓⊢t Γ+@(Γ :: (.(length Γ) , A@(⇒ _ _ _))) .(⇒ _ _ _) .(length Γ) A≠∗ Γ+⊢@(cc Γ⊢ Γ⊢A idp) Γ+⊢A@(ar _ _ _) (var (cc _ _ _) (inr (idp , idp))) =
    var (↓⊢C Γ+ Γ+⊢) (inr (idp , (wk↓T Γ A (length Γ) A Γ⊢A Γ+⊢A ^)))
