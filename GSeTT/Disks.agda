{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules

{- Disk and Sphere contexts - properties -}
module GSeTT.Disks where

  {- Definition of "universal source and target variables" -}
  n-src : ℕ → ℕ
  n-tgt : ℕ → ℕ
  n⇒ : ℕ → Pre-Ty

  n-src O = O
  n-src (S n) = S (n-tgt n)
  n-tgt n = S (n-src n)

  n⇒ O = ∗
  n⇒ (S n) = ⇒ (n⇒ n) (Var (n-src n)) (Var (n-tgt  n))

  {- Syntactic definition of disks and spheres -}
  𝕊 : ℕ → Pre-Ctx
  𝔻 : ℕ → Pre-Ctx

  𝕊 O = nil
  𝕊 (S n) = (𝔻 n) :: (length (𝔻 n) , n⇒ n)
  𝔻 n = (𝕊 n) :: (length (𝕊 n) , n⇒ n)

  𝕊-length : ∀ n → length (𝕊 n) == n-src n
  𝕊-length O = idp
  𝕊-length (S n) = S= (S= (𝕊-length n))

  {- Disk and Sphere context are valid -}
  𝕊⊢ : ∀ n → 𝕊 n ⊢C
  𝔻⊢ : ∀ n → 𝔻 n ⊢C
  𝕊⊢⇒ : ∀ n → 𝕊 n ⊢T n⇒ n

  𝕊⊢ O = ec
  𝕊⊢ (S n) = cc (𝔻⊢ n) (wkT (𝕊⊢⇒ n) (𝔻⊢ n))
  𝔻⊢ n = cc (𝕊⊢ n) (𝕊⊢⇒ n)

  𝕊⊢⇒ O = ob ec
  𝕊⊢⇒ (S n) = ar (wkt (var (𝔻⊢ n) (inr (((𝕊-length n) ^) , idp))) (𝕊⊢ (S n))) (var (𝕊⊢ (S n)) (inr ((S= (𝕊-length n) ^) , idp)))

