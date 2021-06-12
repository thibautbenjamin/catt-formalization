{-# OPTIONS --rewriting --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import Sets ℕ eqdecℕ

{- PS-contexts -}
module CaTT.Ps-contexts where

  {- Rules for PS-contexts -}
  data _⊢ps_#_ : Pre-Ctx → ℕ → Pre-Ty → Set₁ where
    pss : (nil :: (O , ∗)) ⊢ps O # ∗
    psd : ∀ {Γ f A x y} → Γ ⊢ps f # (⇒ A (Var x) (Var y)) → Γ ⊢ps y # A
    pse : ∀ {Γ x A} → Γ ⊢ps x # A → ((Γ :: ((length Γ) , A)) :: (S (length Γ) , ⇒ A (Var x) (Var (length Γ)))) ⊢ps S (length Γ) # ⇒ A (Var x) (Var (length Γ))

  data _⊢ps : Pre-Ctx → Set₁ where
    ps : ∀ {Γ x} → Γ ⊢ps x # ∗ → Γ ⊢ps


  {- PS-contexts define valid contexts -}
  Γ⊢ps→Γ⊢ : ∀ {Γ} → Γ ⊢ps → Γ ⊢C
  Γ⊢psx:A→Γ⊢x:A : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢t (Var x) # A

  Γ⊢ps→Γ⊢ (ps Γ⊢psx) = Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx)
  Γ⊢psx:A→Γ⊢x:A pss = var (cc ec (ob ec) idp) (inr (idp , idp))
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) with Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psf:x⇒y)
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) | ar _ Γ⊢y:A = Γ⊢y:A
  Γ⊢psx:A→Γ⊢x:A (pse Γ⊢psx:A) with (cc (Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)) (Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)) idp)
  ...                          | Γ,y:A⊢ = var (cc Γ,y:A⊢ (ar (wkt (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A) Γ,y:A⊢) (var Γ,y:A⊢ (inr (idp , idp)))) idp) (inr (idp , idp))

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
  srcᵢ-var i pss = if i ≡ 0 then nil else (nil :: 0)
  srcᵢ-var i (psd Γ⊢psx) = srcᵢ-var i Γ⊢psx
  srcᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx) with dec-≤ i (S (dim A))
  ... | inl i≤SdimA = srcᵢ-var i Γ⊢psx
  ... | inr SdimA<i = (srcᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

  drop : ∀ {i} {A : Set i} → list A → list A
  drop nil = nil
  drop (l :: a) = l

  tgtᵢ-var : ∀ {Γ x A} → ℕ → Γ ⊢ps x # A → list ℕ
  tgtᵢ-var i pss = if i ≡ 0 then nil else (nil :: 0)
  tgtᵢ-var i (psd Γ⊢psx) = tgtᵢ-var i Γ⊢psx
  tgtᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx) with dec-≤ i (S (dim A))
  ... | inl i≤SdimA = if i ≡ S (dim A) then drop(tgtᵢ-var i Γ⊢psx) :: length Γ else tgtᵢ-var i Γ⊢psx
  ... | inr SdimA<i = (tgtᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

  -- tgtᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx) with dec-≤ i (S (dim A)) | dec-≤ (S i) (S (dim A))
  -- ... | inl i≤SdimA | inl Si≤SdimA = tgtᵢ-var i Γ⊢psx
  -- ... | inl i≤SdimA | inr SdimA<Si = drop(tgtᵢ-var i Γ⊢psx) :: length Γ
  -- ... | inr SdimA<i | _ = (tgtᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

  src-var : (Γ : ps-ctx) → set
  src-var (Γ , ps Γ⊢psx) = set-of-list (srcᵢ-var (dimC Γ) Γ⊢psx)

  tgt-var : (Γ : ps-ctx) → set
  tgt-var (Γ , ps Γ⊢psx) = set-of-list (tgtᵢ-var (dimC Γ) Γ⊢psx)


  -- It is not necessary to define the pre contexts, as they can be infered with the derivation tree. We do it just as a sanity check
  Pre-Γc : Pre-Ctx
  Pre-Γc = ((((nil :: (0 , ∗)) :: (1 , ∗)) :: (2 , ⇒ ∗ (Var 0) (Var 1))) :: (3 , ∗)) :: (4 , ⇒ ∗ (Var 1) (Var 3))

  Pre-Γw : Pre-Ctx
  Pre-Γw = ((((((nil :: (0 , ∗)) :: (1 , ∗)) :: (2 , ⇒ ∗ (Var 0) (Var 1))) :: (3 , ⇒ ∗ (Var 0) (Var 1))) :: (4 , ⇒ (⇒ ∗ (Var 0) (Var 1)) (Var 2) (Var 3))) :: (5 , ∗)) :: (6 , ⇒ ∗ (Var 1) (Var 5))


  Γc⊢ps : Pre-Γc ⊢ps
  Γc⊢ps = ps (psd (pse (psd (pse pss))))

  Γw⊢ps : Pre-Γw ⊢ps
  Γw⊢ps = ps (psd (pse (psd (psd (pse (pse pss))))))

  Γc : ps-ctx
  Γc = _ , Γc⊢ps

  Γw : ps-ctx
  Γw = _ , Γw⊢ps

  src-Γc : src-var Γc ≗ singleton 0
  src-Γc = (λ x → id) , λ x → id

  tgt-Γc : tgt-var Γc ≗ singleton 3
  tgt-Γc = (λ x → id) , λ x → id

  -- src-Γw : src-var Γw ≗ {!!}
  -- src-Γw = {!!}
