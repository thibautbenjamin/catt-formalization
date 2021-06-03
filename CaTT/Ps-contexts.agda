{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import Sets ℕ eqdecℕ

{- PS-contexts -}
module CaTT.Ps-contexts where

  {- Rules for PS-contexts -}
  data _⊢ps_#_ : Pre-Ctx → ℕ → Pre-Ty → Set where
    pss : (nil :: (O , ∗)) ⊢ps O # ∗
    psd : ∀ {Γ f A x y} → Γ ⊢ps f # (⇒ A (Var x) (Var y)) → Γ ⊢ps y # A
    pse : ∀ {Γ x A} → Γ ⊢ps x # A → ((Γ :: ((length Γ) , A)) :: (S (length Γ) , ⇒ A (Var x) (Var (length Γ)))) ⊢ps S (length Γ) # ⇒ A (Var x) (Var (length Γ))

  data _⊢ps : Pre-Ctx → Set where
    ps : ∀ {Γ x} → (Γ :: (x , ∗)) ⊢ps x # ∗ → (Γ :: (x , ∗)) ⊢ps


  {- PS-contexts define valid contexts -}
  Γ⊢ps→Γ⊢ : ∀ {Γ} → Γ ⊢ps → Γ ⊢C
  Γ⊢psx:A→Γ⊢x:A : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢t (Var x) # A

  Γ⊢ps→Γ⊢ (ps Γ⊢psx) = Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx)
  Γ⊢psx:A→Γ⊢x:A pss = var (cc ec (ob ec)) (inr (idp , idp))
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) with Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psf:x⇒y)
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) | ar _ Γ⊢y:A = Γ⊢y:A
  Γ⊢psx:A→Γ⊢x:A (pse Γ⊢psx:A) with (cc (Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)) (Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)))
  ...                          | Γ,y:A⊢ = var (cc Γ,y:A⊢ (ar (wkt (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A) Γ,y:A⊢) (var Γ,y:A⊢ (inr (idp , idp))))) (inr (idp , idp))

  Γ⊢psx:A→Γ⊢ : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢C
  Γ⊢psx:A→Γ⊢ Γ⊢psx:A = Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)

  -- some renamings so that useful lemmas are faster to write
  -- TODO restrict these as local names
  psv : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢C --psvalid
  psv Γ⊢ps = Γ⊢psx:A→Γ⊢ Γ⊢ps

  psvar : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢t (Var x) # A
  psvar Γ⊢psx = Γ⊢psx:A→Γ⊢x:A Γ⊢psx

  ps-ctx : Set₁
  ps-ctx = Σ Pre-Ctx (λ Γ → Γ ⊢ps)

  {- Eric's trick : is a src-var -}
  srcᵢ-var : ∀ {Γ x A} → ℕ → Γ ⊢ps x # A → list ℕ
  srcᵢ-var i pss = nil :: 0
  srcᵢ-var i (psd Γ⊢psx) = srcᵢ-var i Γ⊢psx
  srcᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx) with dec-≤ i (dim A)
  ... | inl i≤dimA = srcᵢ-var i Γ⊢psx
  ... | inr dimA<i = (srcᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

  drop : ∀ {i} {A : Set i} → list A → list A
  drop nil = nil
  drop (l :: a) = l

  tgtᵢ-var : ∀ {Γ x A} → ℕ → Γ ⊢ps x # A → list ℕ
  tgtᵢ-var i pss = nil :: 0
  tgtᵢ-var i (psd Γ⊢psx) = tgtᵢ-var i Γ⊢psx
  tgtᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx) with dec-≤ i (dim A) | dec-≤ (S i) (dim A)
  ... | inl i≤dimA | inl Si≤dimA = tgtᵢ-var i Γ⊢psx
  ... | inl i≤dimA | inr dimA<Si = drop(tgtᵢ-var i Γ⊢psx) :: length Γ
  ... | inr dimA<i | _ = (tgtᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

  src-var : ∀ Γ → Γ ⊢ps → set
  src-var Γ (ps Γ⊢psx) = set-of-list (srcᵢ-var (dimC Γ) Γ⊢psx)

  tgt-var : ∀ Γ → Γ ⊢ps → set
  tgt-var Γ (ps Γ⊢psx) = set-of-list (tgtᵢ-var (dimC Γ) Γ⊢psx)
