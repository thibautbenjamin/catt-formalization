{-# OPTIONS --rewriting --allow-unsolved-metas #-}

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

  𝔻0-var : ∀ x A → 𝔻 0 ⊢t (Var x) # A → x == 0
  𝔻0-var x A (var _ (inr (idp , _))) = idp

  dec-⊢psx : ∀ Γ x A → dec (Γ ⊢ps x # A)
  dec-⊢psx nil x A = inr λ{∅⊢psx → ∅-is-not-ps x A ∅⊢psx}
  dec-⊢psx Γ@(nil :: (n , ⇒ _ _ _)) x A with dec-⊢C Γ
  ... | inr ¬Γ⊢ = inr λ Γ⊢ps → ¬Γ⊢ (psv Γ⊢ps)
  ... | inl (cc _ ∅⊢⇒) with ∅-⊢T _ ∅⊢⇒
  ... | ()
  dec-⊢psx (nil :: (O , ∗)) x A with eqdecℕ O x | eqdec-PreTy ∗ A
  ... | inl idp | inl idp = inl pss
  ... | inl idp | inr A≠∗ = inr λ {Γ⊢ps0 → A≠∗ (unique-type (var (psv Γ⊢ps0) (inr (idp , idp))) (psvar Γ⊢ps0) idp)}
  ... | inr x≠0 | _ = inr λ{Γ⊢psx → x≠0 ((𝔻0-var x A (psvar Γ⊢psx)) ^)}
  dec-⊢psx Γ@(nil :: (S n , ∗)) x A with dec-⊢C Γ
  ... | inr ¬Γ⊢ = inr λ Γ⊢ps → ¬Γ⊢ (psv Γ⊢ps)
  dec-⊢psx ((Γ :: (y , B)) :: (z , C)) x A = {!!}

  dec-⊢ps : ∀ Γ → dec (Γ ⊢ps)
  dec-⊢ps nil = inr λ{()}
  dec-⊢ps (Γ :: (x , ∗)) with dec-⊢psx (Γ :: (x , ∗)) x ∗
  ... | inl Γ⊢psx = inl (ps Γ⊢psx)
  ... | inr ¬Γ⊢psx = inr λ{ (ps Γ⊢psx) → ¬Γ⊢psx Γ⊢psx}
  dec-⊢ps (Γ :: (x , ⇒ _ _ _)) = inr λ{()}
