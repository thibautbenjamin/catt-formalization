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
    pse : ∀ {Γ x A y z C t Tt} → Γ ⊢ps x # A  →  y == length Γ → z == S (length Γ) → C == ⇒ A (Var x) (Var y) → z == t → C == Tt → ((Γ :: (y , A)) :: (z , C)) ⊢ps t # Tt

  data _⊢ps : Pre-Ctx → Set₁ where
    ps : ∀ {Γ x} → Γ ⊢ps x # ∗ → Γ ⊢ps

  psd↓ : ∀ {Γ f A x y z} → (Γ⊢ps₁ : Γ ⊢ps f # (⇒ A (Var x) (Var z))) → (Γ⊢ps₂ : Γ ⊢ps f # (⇒ A (Var y) (Var z))) → (p : x == y) → transport p Γ⊢ps₁ == Γ⊢ps₂ → psd Γ⊢ps₁ == psd Γ⊢ps₂
  psd↓ Γ⊢ps₁ .Γ⊢ps₁ idp idp = idp

  pse↓ : ∀ {Γ A B C x y a f z} → (Γ⊢ps₁ : Γ ⊢ps x # A) (a= : a == length Γ) (f= : f == S (length Γ)) (B= : B == ⇒ A (Var x) (Var a)) (z= : f == z) (C= : B == C)
                                → (Γ⊢ps₂ : Γ ⊢ps y # A) (a=' : a == length Γ) (f=' : f == S (length Γ)) (B=' : B == ⇒ A (Var y) (Var a)) (z=' : f == z) (C=' : B == C)
                                → (p : x == y)  → transport p Γ⊢ps₁ == Γ⊢ps₂ → (pse Γ⊢ps₁ a= f= B= z= C=) == (pse Γ⊢ps₂ a=' f=' B=' z=' C=')
  pse↓ _ _ _ _ _ _ _ _ _ _ _ _ idp idp = ap⁶ pse idp (is-prop-has-all-paths (is-setℕ _ _) _ _)
                                                      (is-prop-has-all-paths (is-setℕ _ _) _ _)
                                                      (is-prop-has-all-paths (eqdec-is-set eqdec-PreTy _ _) _ _)
                                                      (is-prop-has-all-paths (is-setℕ _ _) _ _)
                                                      (is-prop-has-all-paths (eqdec-is-set eqdec-PreTy _ _) _ _)


  ps↓ : ∀ {Γ x y} → (Γ⊢ps₁ : Γ ⊢ps x # ∗) → (Γ⊢ps₂ : Γ ⊢ps y # ∗)
                  → (p : x == y)  → transport {B = λ z → Γ ⊢ps z # ∗} p Γ⊢ps₁ == Γ⊢ps₂ → (ps Γ⊢ps₁) == (ps Γ⊢ps₂)
  ps↓ _ _ idp idp = idp


  {- PS-contexts define valid contexts -}
  Γ⊢ps→Γ⊢ : ∀ {Γ} → Γ ⊢ps → Γ ⊢C
  Γ⊢psx:A→Γ⊢x:A : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢t (Var x) # A

  Γ⊢ps→Γ⊢ (ps Γ⊢psx) = Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx)
  Γ⊢psx:A→Γ⊢x:A pss = var (cc ec (ob ec) idp) (inr (idp , idp))
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) with Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psf:x⇒y)
  Γ⊢psx:A→Γ⊢x:A (psd Γ⊢psf:x⇒y) | ar _ Γ⊢y:A = Γ⊢y:A
  Γ⊢psx:A→Γ⊢x:A (pse Γ⊢psx:A idp idp idp idp idp) with (cc (Γ⊢t:A→Γ⊢ (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)) (Γ⊢t:A→Γ⊢A (Γ⊢psx:A→Γ⊢x:A Γ⊢psx:A)) idp)
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
  srcᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx idp idp idp idp idp) with dec-≤ i (S (dim A))
  ... | inl i≤SdimA = srcᵢ-var i Γ⊢psx
  ... | inr SdimA<i = (srcᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

  drop : ∀ {i} {A : Set i} → list A → list A
  drop nil = nil
  drop (l :: a) = l

  tgtᵢ-var : ∀ {Γ x A} → ℕ → Γ ⊢ps x # A → list ℕ
  tgtᵢ-var i pss = if i ≡ 0 then nil else (nil :: 0)
  tgtᵢ-var i (psd Γ⊢psx) = tgtᵢ-var i Γ⊢psx
  tgtᵢ-var i (pse {Γ = Γ} {A = A} Γ⊢psx idp idp idp idp idp) with dec-≤ i (S (dim A))
  ... | inl i≤SdimA = if i ≡ S (dim A) then drop(tgtᵢ-var i Γ⊢psx) :: length Γ else tgtᵢ-var i Γ⊢psx
  ... | inr SdimA<i = (tgtᵢ-var i Γ⊢psx :: length Γ) :: (S (length Γ))

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
  Γc⊢ps = ps (psd (pse (psd (pse pss idp idp idp idp idp)) idp idp idp idp idp))

  Γw⊢ps : Pre-Γw ⊢ps
  Γw⊢ps = ps (psd (pse (psd (psd (pse (pse pss idp idp idp idp idp) idp idp idp idp idp))) idp idp idp idp idp))

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

-- TODO : cleanup and unite these two lemmas
  x∉ : ∀ {Γ x} → Γ ⊢C → length Γ ≤ x → (∀ {A} → ¬ (Γ ⊢t (Var x) # A))
  x∉ (cc Γ⊢ _ idp) l≤x (var _ (inl x∈Γ)) = x∉ Γ⊢ (Sn≤m→n≤m l≤x) (var Γ⊢ x∈Γ)
  x∉ (cc Γ⊢ _ idp) l≤x (var _ (inr (idp , idp))) = Sn≰n _ l≤x

  l∉ : ∀ {Γ x} → Γ ⊢C → length Γ ≤ x → ¬ (x ∈ Γ)
  l∉ (cc Γ⊢ _ idp) l≤x (inl x∈Γ) = l∉ Γ⊢ (Sn≤m→n≤m l≤x) x∈Γ
  l∉ (cc Γ⊢ _ idp) l≤x (inr idp) = Sn≰n _ l≤x
