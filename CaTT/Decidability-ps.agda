{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Disks
open import GSeTT.Uniqueness-Derivations
open import GSeTT.Dec-Type-Checking
open import CaTT.Ps-contexts


module CaTT.Decidability-ps where
  ∅-is-not-ps : ∀ x A → ¬ (nil ⊢ps x # A)
  ∅-is-not-ps x A ∅⊢psx with psvar ∅⊢psx
  ... | var _ ()

  ∅-⊢T : ∀ A → nil ⊢T A → A == ∗
  ∅-⊢T = {!!}

  ¬ps-ends-by-object : ∀ {Γ x y A} → Γ ≠ nil → ¬ ((Γ :: (x , ∗)) ⊢ps y # A)
  ¬ps-ends-by-object Γ≠nil pss = Γ≠nil idp
  ¬ps-ends-by-object Γ≠nil (psd Γ⊢ps) = ¬ps-ends-by-object Γ≠nil Γ⊢ps

  ¬ps-carrier : ∀ {Γ x y z A B C} → (∀ a → B ≠ ⇒ A a (Var x)) → ¬ (((Γ :: (x , A)) :: (y , B)) ⊢ps z # C)
  ¬ps-carrier = {!!}

  Γ+⊢ps→Γ⊢ps : ∀ {Γ x A a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) ⊢ps x # A → Γ ⊢ps a # B
  Γ+⊢ps→Γ⊢ps = {!!}

  last-ps-var : ∀ {Γ x A a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) ⊢ps x # A → z == S (length Γ)
  last-ps-var = {!!}

  previous-to-last-ps-var : ∀ {Γ x A a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) ⊢ps x # A → y == length Γ
  previous-to-last-ps-var = {!!}



  𝔻0-var : ∀ x A → 𝔻 0 ⊢t (Var x) # A → x == 0
  𝔻0-var x A (var _ (inr (idp , _))) = idp

  ⊢psx→⊢ps : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢ps
  ⊢psx→⊢ps = {!!}

  dec-tgt : ∀ {Γ x A} → dec (Σ (ℕ × ℕ) (λ (a , f) → Γ ⊢t Var f # ⇒ A (Var a) (Var x)))
  dec-tgt = {!!}

  dec-⊢psx : ∀ Γ x A → dec (Γ ⊢ps x # A)
  dec-⊢psx-aux : ∀ Γ x A y B z C → dim A ≤ dim C → dec (((Γ :: (y , B)) :: (z , C)) ⊢ps x # A)

  dec-⊢psx nil x A = inr λ{∅⊢psx → ∅-is-not-ps x A ∅⊢psx}
  dec-⊢psx Γ@(nil :: (n , ⇒ _ _ _)) x A with dec-⊢C Γ
  ... | inr ¬Γ⊢ = inr λ Γ⊢ps → ¬Γ⊢ (psv Γ⊢ps)
  ... | inl (cc _ ∅⊢⇒ idp) with ∅-⊢T _ ∅⊢⇒
  ... | ()
  dec-⊢psx (nil :: (O , ∗)) x A with eqdecℕ O x | eqdec-PreTy ∗ A
  ... | inl idp | inl idp = inl pss
  ... | inl idp | inr A≠∗ = inr λ {Γ⊢ps0 → A≠∗ (unique-type (var (psv Γ⊢ps0) (inr (idp , idp))) (psvar Γ⊢ps0) idp)}
  ... | inr x≠0 | _ = inr λ{Γ⊢psx → x≠0 ((𝔻0-var x A (psvar Γ⊢psx)) ^)}
  dec-⊢psx Γ@(nil :: (S n , ∗)) x A with dec-⊢C Γ
  ... | inl (cc Γ⊢ x₁ ())
  ... | inr ¬Γ⊢ = inr λ Γ⊢ps → ¬Γ⊢ (psv Γ⊢ps)
  dec-⊢psx ((Γ :: (y , B)) :: (z , C)) x A with C
  ... | ∗ = inr (λ Γ⊢ps → ¬ps-carrier (λ _ → λ{()}) Γ⊢ps)
  ... | ⇒ B' a (Var y') with eqdec-PreTy B B' | eqdecℕ y y'
  ... | inl idp | inl idp = {!!}
  ... | inl idp | inr y≠y' = inr (λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → y≠y' (=Var (snd (=⇒ eq)) ^)) Γ⊢ps)
  ... | inr B≠B' | _ = inr λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → B≠B' (fst (fst (=⇒ eq)) ^)) Γ⊢ps

  dec-⊢psx-aux Γ x A y B z C dimA≤dimC with C
  ... | ∗ = inr (λ Γ⊢ps → ¬ps-carrier (λ _ → λ{()}) Γ⊢ps)
  ... | ⇒ B' (Var a) (Var y') with eqdec-PreTy B B' | eqdecℕ y y'
  ... | inr B≠B' | _ = inr λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → B≠B' (fst (fst (=⇒ eq)) ^)) Γ⊢ps
  ... | inl idp | inr y≠y' = inr (λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → y≠y' (=Var (snd (=⇒ eq)) ^)) Γ⊢ps)
  ... | inl idp | inl idp with dec-⊢psx Γ a B'
  ... | inr ¬Γ⊢ps = inr λ Γ+⊢ps → ¬Γ⊢ps (Γ+⊢ps→Γ⊢ps Γ+⊢ps)
  ... | inl Γ⊢ps with eqdecℕ z (S (length Γ)) | eqdecℕ y (length Γ)
  ... | inr z≠SlΓ | _ = inr λ Γ+⊢ps → z≠SlΓ (last-ps-var Γ+⊢ps)
  ... | inl idp | inr y≠lΓ = inr λ Γ+⊢ps → y≠lΓ (previous-to-last-ps-var Γ+⊢ps)
  ... | inl idp | inl idp with eqdecℕ x (S (length Γ))
  ... | inr x≠SlΓ = {!!}
  ... | inl idp with eqdec-PreTy A (⇒ B' (Var a) (Var y'))
  ... | inl idp = inl (pse Γ⊢ps)
  ... | inr A≠⇒ = inr λ Γ+⊢ps → A≠⇒ (unique-type (psvar Γ+⊢ps) (var (psv Γ+⊢ps) (inr (idp , idp))) idp)

  Γ⊢psx→x≤lΓ : ∀ {Γ x A} → Γ ⊢ps x # A → x ≤ length Γ
  Γ⊢psx→x≤lΓ = {!!}

  dec-⊢ps-aux : ∀ Γ k → dec (Σ ℕ (λ x → ((Γ ⊢ps x # ∗) × (x ≤ k))))
  dec-⊢ps-aux₁ : ∀ {Γ k} → ¬ (Γ ⊢ps S k # ∗) → ¬ (Σ ℕ (λ x → ((Γ ⊢ps x # ∗) × (x ≤ k)))) → ¬ (Σ ℕ (λ x → ((Γ ⊢ps x # ∗) × (x ≤ S k))))
  dec-⊢ps-aux Γ O with dec-⊢psx Γ O ∗
  ... | inl Γ⊢psO = inl (0 , (Γ⊢psO , n≤n _))
  ... | inr ¬Γ⊢psO = inr λ{(.O , (Γ⊢psO , (0≤ O))) → ¬Γ⊢psO Γ⊢psO}
  dec-⊢ps-aux Γ (S k) with dec-⊢psx Γ (S k) ∗
  ... | inl Γ⊢psx = inl (S k , (Γ⊢psx , n≤n _))
  ... | inr ¬Γ⊢psSk with dec-⊢ps-aux Γ k
  ... | inl (i , (Γ⊢psi , i≤k)) = inl (i , (Γ⊢psi , n≤m→n≤Sm i≤k))
  ... | inr H = inr λ {(i , (Γ⊢psi , i≤Sk)) → dec-⊢ps-aux₁ ¬Γ⊢psSk H (i , (Γ⊢psi , i≤Sk))}
  dec-⊢ps-aux₁ ¬Γ⊢psSk H (i , (Γ⊢psi , i≤Sk)) with ≤S _ _ i≤Sk
  ... | inl i≤k = H (i , (Γ⊢psi , i≤k))
  ... | inr idp = ¬Γ⊢psSk Γ⊢psi

  dec-⊢ps : ∀ Γ → dec (Γ ⊢ps)
  dec-⊢ps Γ with dec-⊢ps-aux Γ (length Γ)
  ... | inl (x , (Γ⊢psx , _)) = inl (ps Γ⊢psx)
  ... | inr H = inr λ {(ps {x = x} Γ⊢psx) → H (x , (Γ⊢psx , Γ⊢psx→x≤lΓ Γ⊢psx))}

