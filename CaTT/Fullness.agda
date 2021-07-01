{-# OPTIONS --rewriting --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Disks
open import CaTT.Ps-contexts
open import CaTT.Uniqueness-Derivations-Ps
open import Sets ℕ eqdecℕ

module CaTT.Fullness where

  data Ty : Set₁
  data Tm : Set₁
  data Sub : Set₁

  data _is-full-in_ : Ty → ps-ctx → Set₁

  data Ty where
    ∗ : Ty
    ⇒ : Ty → Tm → Tm → Ty
  data Tm where
    v : ℕ → Tm
    coh : (Γ : ps-ctx) → (A : Ty) → A is-full-in Γ → Sub  → Tm
  data Sub where
    <> : Sub
    <_,_↦_> : Sub → ℕ → Tm → Sub

  =⇒Ty : ∀ {A A' : Ty} {t t' u u' : Tm} → _==_ {A = Ty} (⇒ A t u) (⇒ A' t' u') → ((A == A' × t == t') × u == u')
  =⇒Ty idp = (idp , idp) , idp

  coh= : ∀ {Γ Γ' A A' Afull A'full γ γ'} → coh Γ A Afull γ == coh Γ' A' A'full γ' → ((Γ == Γ' × A == A') × γ == γ')
  coh= idp = (idp , idp) , idp

  <>= : ∀ {γ γ' x x' t t'} → < γ , x ↦ t > == < γ' , x' ↦ t' > → ((γ == γ' × x == x') × t == t')
  <>= idp = (idp , idp) , idp

  {- Set of variables -}
  varC : Pre-Ctx → set
  varC nil = Ø
  varC (Γ :: (x , _)) = (varC Γ) ∪-set (singleton x)

  varT : Ty → set
  vart : Tm → set
  varS : Sub → set

  varT ∗ = Ø
  varT (⇒ A t u) = (varT A) ∪-set ((vart t) ∪-set (vart u))
  vart (v x) = singleton x
  vart (coh Γ A Afull γ) = varS γ
  varS <> = Ø
  varS < γ , x ↦ t > = (varS γ) ∪-set (vart t)


  {- fullness condition -}
  data _is-full-in_ where
    side-cond₁ : ∀ Γ A t u → (src-var Γ) ≗ ((varT A) ∪-set (vart t)) → (tgt-var Γ) ≗ ((varT A) ∪-set (vart u)) → (⇒ A t u) is-full-in Γ
    side-cond₂ : ∀ Γ A →  (varC (fst Γ)) ≗ (varT A) → A is-full-in Γ

  ∈-drop : ∀ {A : Set} {a : A} {l : list A} → a ∈-list drop l → a ∈-list l
  ∈-drop {A} {a} {l :: a₁} x = inl x


  l∉∂⁻ : ∀ {Γ i x A y} → (Γ⊢ps : Γ ⊢ps x # A) → length Γ ≤ y → ¬ (y ∈-list (srcᵢ-var i Γ⊢ps))
  l∉∂⁻ {i = i} pss lΓ≤y y∈ with eqdecℕ i O
  ... | inl _ = y∈
  l∉∂⁻ {i = i} pss lΓ≤y (inr idp) | inr _ = Sn≰n _ lΓ≤y
  l∉∂⁻ (psd Γ⊢ps) lΓ≤y y∈ = l∉∂⁻ Γ⊢ps lΓ≤y y∈
  l∉∂⁻ {i = i} (pse {A = A} Γ⊢ps idp idp idp idp idp) SSl≤y y∈ with dec-≤ i (S (dim A))
  ... | inl _ = l∉∂⁻ Γ⊢ps (Sn≤m→n≤m (Sn≤m→n≤m SSl≤y)) y∈
  l∉∂⁻ {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inl (inl y∈)) | inr _ = l∉∂⁻ Γ⊢ps (Sn≤m→n≤m (Sn≤m→n≤m SSl≤y)) y∈
  l∉∂⁻ {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inl (inr idp)) | inr _ = Sn≰n _ (n≤m→n≤Sm SSl≤y)
  l∉∂⁻ {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inr idp) | inr _ = Sn≰n _ SSl≤y

  l∉∂⁺ : ∀ {Γ i x A y} → (Γ⊢ps : Γ ⊢ps x # A) → length Γ ≤ y → ¬ (y ∈-list (tgtᵢ-var i Γ⊢ps))
  l∉∂⁺ {i = i} pss lΓ≤y y∈ with eqdecℕ i O
  ... | inl _ = y∈
  l∉∂⁺ {i = i} pss lΓ≤y (inr idp) | inr _ = Sn≰n _ lΓ≤y
  l∉∂⁺ (psd Γ⊢ps) lΓ≤y y∈ = l∉∂⁺ Γ⊢ps lΓ≤y y∈
  l∉∂⁺ {i = i} (pse {A = A} Γ⊢ps idp idp idp idp idp) SSl≤y y∈ with dec-≤ i (S (dim A))
  l∉∂⁺ {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inl (inl y∈)) | inr _ = l∉∂⁺ Γ⊢ps (Sn≤m→n≤m (Sn≤m→n≤m SSl≤y)) y∈
  l∉∂⁺ {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inl (inr idp)) | inr _ = Sn≰n _ (n≤m→n≤Sm SSl≤y)
  l∉∂⁺ {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inr idp) | inr x = Sn≰n _ SSl≤y
  ... | inl _ with eqdecℕ i (S (dim A))
  l∉∂⁺ {i = .(S (dim _))} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inl y∈drop) | inl _ | inl idp = l∉∂⁺ Γ⊢ps (Sn≤m→n≤m (Sn≤m→n≤m SSl≤y)) (∈-drop y∈drop)
  l∉∂⁺ {i = .(S (dim _))} (pse {A = _} Γ⊢ps idp idp idp idp idp) SSl≤y (inr idp) | inl _ | inl idp = Sn≰n _ (n≤m→n≤Sm SSl≤y)
  ... | inr _ = l∉∂⁺ Γ⊢ps (Sn≤m→n≤m (Sn≤m→n≤m SSl≤y)) y∈

  ∂⁻ᵢ-var : ∀ {Γ x A y B i} → (Γ⊢ps : Γ ⊢ps x # A)  → Γ ⊢t (Var y) # B → i ≤ dim B → ¬ (y ∈-list (srcᵢ-var i Γ⊢ps))
  ∂⁻ᵢ-var pss (var x (inr (idp , idp))) (0≤ .0) ()
  ∂⁻ᵢ-var (psd Γ⊢ps) Γ⊢y i≤B y∈∂⁻ = ∂⁻ᵢ-var Γ⊢ps Γ⊢y i≤B y∈∂⁻
  ∂⁻ᵢ-var {i = i} (pse {A = A} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B y∈∂⁻ with dec-≤ i (S (dim A))
  ... | inl _ = ∂⁻ᵢ-var Γ⊢ps (var (psv Γ⊢ps) y∈Γ) i≤B y∈∂⁻
  ∂⁻ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inl (inl y∈∂⁻)) | inr _ = ∂⁻ᵢ-var Γ⊢ps (var (psv Γ⊢ps) y∈Γ) i≤B y∈∂⁻
  ∂⁻ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inl (inr idp)) | inr _ = x∉ (psv Γ⊢ps) (n≤n _) (var (psv Γ⊢ps) y∈Γ)
  ∂⁻ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inr idp) | inr _ = x∉ (psv Γ⊢ps) (n≤Sn _) (var (psv Γ⊢ps) y∈Γ)
  ∂⁻ᵢ-var {i = i} (pse {A = B} Γ⊢ps idp idp idp idp idp) (var _ (inl (inr (idp , idp)))) i≤B y∈∂⁻ with dec-≤ i (S (dim B))
  ... | inl _ = l∉∂⁻ Γ⊢ps (n≤n _) y∈∂⁻
  ... | inr i≰SB = i≰SB (n≤m→n≤Sm i≤B)
  ∂⁻ᵢ-var {i = i} (pse {A = A} Γ⊢ps idp idp idp idp idp) (var _ (inr (idp , idp))) i≤SA y∈∂⁻ with dec-≤ i (S (dim A))
  ... | inl _ = l∉∂⁻ Γ⊢ps (n≤Sn _) y∈∂⁻
  ... | inr i≰SA = i≰SA i≤SA

  ∂⁺ᵢ-var : ∀ {Γ x A y B i} → (Γ⊢ps : Γ ⊢ps x # A)  → Γ ⊢t (Var y) # B → i ≤ dim B → ¬ (y ∈-list (tgtᵢ-var i Γ⊢ps))
  ∂⁺ᵢ-var pss (var x (inr (idp , idp))) (0≤ .0) ()
  ∂⁺ᵢ-var (psd Γ⊢ps) Γ⊢y i≤B y∈∂⁺ = ∂⁺ᵢ-var Γ⊢ps Γ⊢y i≤B y∈∂⁺
  ∂⁺ᵢ-var {i = i} (pse {A = A} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B y∈∂⁺ with dec-≤ i (S (dim A))
  ... | inl i≤SdimA with eqdecℕ i (S (dim A))
  ... | inr _ = ∂⁺ᵢ-var Γ⊢ps (var (psv Γ⊢ps) y∈Γ) i≤B y∈∂⁺
  ∂⁺ᵢ-var {i = .(S (dim _))} (pse {A = A}  Γ⊢ps idp idp idp idp idp) (var {x = y} _ (inl (inl y∈Γ))) i≤B (inl y∈drop) | inl i≤SdimA | inl idp = ∂⁺ᵢ-var Γ⊢ps (var (psv Γ⊢ps) y∈Γ) i≤B (∈-drop y∈drop)
  ∂⁺ᵢ-var {i = .(S (dim _))} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inr idp) | inl i≤SdimA | inl idp = lΓ∉Γ (psv Γ⊢ps) y∈Γ
  ∂⁺ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inl (inl y∈∂⁻)) | inr _ = ∂⁺ᵢ-var Γ⊢ps (var (psv Γ⊢ps) y∈Γ) i≤B y∈∂⁻
  ∂⁺ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inl (inr idp)) | inr _ = x∉ (psv Γ⊢ps) (n≤n _) (var (psv Γ⊢ps) y∈Γ)
  ∂⁺ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inl (inl y∈Γ))) i≤B (inr idp) | inr _ = x∉ (psv Γ⊢ps) (n≤Sn _) (var (psv Γ⊢ps) y∈Γ)
  ∂⁺ᵢ-var {i = i} (pse {A = B} Γ⊢ps idp idp idp idp idp) (var _ (inl (inr (idp , idp)))) i≤B y∈∂⁺ with dec-≤ i (S (dim B))
  ... | inr i≰SB = i≰SB (n≤m→n≤Sm i≤B)
  ... | inl _  with eqdecℕ i (S (dim B))
  ... | inr _ = l∉∂⁺ Γ⊢ps (n≤n _) y∈∂⁺
  ∂⁺ᵢ-var (pse Γ⊢ps idp idp idp idp idp) (var _ (inl (inr (idp , idp)))) i≤B (inl l∈drop) | inl _ | inl _ = l∉∂⁺ Γ⊢ps (n≤n _) (∈-drop l∈drop)
  ∂⁺ᵢ-var (pse Γ⊢ps idp idp idp idp idp) (var _ (inl (inr (idp , idp)))) i≤B (inr p) | inl _ | inl idp = Sn≰n _ i≤B
  ∂⁺ᵢ-var {i = i} (pse {A = A} Γ⊢ps idp idp idp idp idp) (var _ (inr (idp , idp))) i≤SA y∈∂⁺ with dec-≤ i (S (dim A))
  ... | inr i≰SA = i≰SA i≤SA
  ... | inl _ with eqdecℕ i (S (dim A))
  ... | inr _ = l∉∂⁺ Γ⊢ps (n≤Sn _) y∈∂⁺
  ∂⁺ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inr (idp , idp))) i≤SA (inl Sl∈drop) | inl _ | inl _ = l∉∂⁺ Γ⊢ps (n≤Sn _) (∈-drop Sl∈drop)
  ∂⁺ᵢ-var {i = i} (pse {A = _} Γ⊢ps idp idp idp idp idp) (var _ (inr (idp , idp))) i≤SA (inr Sl=l) | inl _ | inl _ = Sn≠n _ Sl=l

  ∈-varC : ∀ {Γ x A} →  x # A ∈ Γ → x ∈-set (varC Γ)
  ∈-varC {Γ :: (y , B)} {x} {A} (inl x∈Γ) = ∈-∪₁ {A = varC Γ} {B = singleton y} (∈-varC x∈Γ)
  ∈-varC {Γ :: (y , B)} {x} {A} (inr (idp , _)) = ∈-∪₂ {A = varC Γ} {B = singleton y} (∈-singleton y)

  max-var-def : Pre-Ctx → ℕ × Pre-Ty
  max-var-def nil = 0 , ∗
  max-var-def (Γ :: (y , B)) with dec-≤ (dimC Γ) (dim B)
  ... | inr _ = max-var-def Γ
  ... | inl _ = y , B

  max-var-is-max : ∀ {Γ} → Γ ≠ nil → Γ ⊢C → let (x , A) = max-var-def Γ in ((x # A ∈ Γ) × (dimC Γ == dim A))
  max-var-is-max {nil} Γ≠nil _ = ⊥-elim (Γ≠nil idp)
  max-var-is-max {Γ :: (y , B)} _ Γ⊢ with dec-≤ (dimC Γ) (dim B)
  ... | inl _ = inr (idp , idp) , idp
  ... | inr _ with Γ
  max-var-is-max {Γ :: (y , B)} _ (cc Γ⊢ Γ⊢B idp) | inr _ | Δ :: (x , A) = let (x∈ , dimA) = max-var-is-max (λ{()}) Γ⊢ in inl x∈ , dimA
  max-var-is-max {Γ :: (.0 , .∗)} _ (cc Γ⊢ (ob _) idp) | inr _ | nil = inr (idp , idp) , idp
  max-var-is-max {Γ :: (.0 , _)} _ (cc Γ⊢ (ar _ _) idp) | inr dΓ≤dB | nil = ⊥-elim (dΓ≤dB (0≤ _))

  psx-nonul : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ≠ nil
  psx-nonul (psd x) idp = psx-nonul x idp

  ps-nonul : ∀ {Γ} → Γ ⊢ps → Γ ≠ nil
  ps-nonul (ps Γ⊢ps) = psx-nonul Γ⊢ps

  max-var : ∀ {Γ} → Γ ⊢ps → Σ (ℕ × Pre-Ty) λ {(x , A) → (x # A ∈ Γ) × (dimC Γ == dim A)}
  max-var {Γ} Γ⊢ps@(ps Γ⊢psx) = max-var-def Γ , max-var-is-max (ps-nonul Γ⊢ps) (psv Γ⊢psx)

  ∂Γ-not-full : ∀ Γ → ¬ (varC (fst Γ) ⊂ ((src-var Γ) ∪-set (tgt-var Γ)))
  ∂Γ-not-full (Γ , Γ⊢ps@(ps Γ⊢psx)) vΓ⊂∂ = let ((x , A) , (x∈Γ , dimA)) = max-var Γ⊢ps in
    ∉-∪ {set-of-list (srcᵢ-var (dimC Γ) Γ⊢psx)} {set-of-list (tgtᵢ-var (dimC Γ) Γ⊢psx)} {x}
    (λ x∈∂⁻ → ∂⁻ᵢ-var Γ⊢psx (var (psv Γ⊢psx) x∈Γ) (≤-= (n≤n _) dimA) (∈-set-∈-list _ _ x∈∂⁻))
    (λ x∈∂⁺ → ∂⁺ᵢ-var Γ⊢psx (var (psv Γ⊢psx) x∈Γ) (≤-= (n≤n _) dimA) (∈-set-∈-list _ _ x∈∂⁺))
    (vΓ⊂∂ x (∈-varC x∈Γ))

  disjoint-cond : ∀ Γ A t u → (src-var Γ) ≗ ((varT A) ∪-set (vart t)) → (tgt-var Γ) ≗ ((varT A) ∪-set (vart u)) → ¬ (varC (fst Γ) ≗ varT (⇒ A t u))
  disjoint-cond Γ A t u (_ , A⊂∂⁻) (_ , A⊂∂⁺) (Γ⊂A , _) =
    let vA = varT A in let vt = vart t in let vu = vart u in
    let sr = src-var Γ in let tg = tgt-var Γ in
    ∂Γ-not-full Γ
      (⊂-trans {varC (fst Γ)} {vA ∪-set (vt ∪-set vu)} {sr ∪-set tg} Γ⊂A
      (≗-⊂ {vA ∪-set (vt ∪-set vu)} {(vA ∪-set vt) ∪-set (vA ∪-set vu)} {sr ∪-set tg} (∪-factor (varT A) (vart t) (vart u))
      (⊂-∪ {vA ∪-set vt} {sr} {vA ∪-set vu} {tg} A⊂∂⁻ A⊂∂⁺)))

  side-cond₁= : ∀ Γ A t u ∂⁻-full₁ ∂⁻-full₂ ∂⁺-full₁ ∂⁺-full₂ → ∂⁻-full₁ == ∂⁻-full₂ → ∂⁺-full₁ == ∂⁺-full₂ → side-cond₁ Γ A t u ∂⁻-full₁ ∂⁺-full₁ == side-cond₁ Γ A t u ∂⁻-full₂ ∂⁺-full₂
  side-cond₁= Γ A t u ∂⁻-full₁ .∂⁻-full₁ ∂⁺-full₁ .∂⁺-full₁ idp idp = idp

  has-all-paths-is-full : ∀ Γ A → has-all-paths (A is-full-in Γ)
  has-all-paths-is-full Γ .(⇒ A t u) (side-cond₁ .Γ A t u x x₁) (side-cond₁ .Γ .A .t .u x₂ x₃) = ap² (λ ∂⁻ → λ ∂⁺ → side-cond₁ Γ A t u ∂⁻ ∂⁺) (is-prop-has-all-paths (is-prop-≗ (src-var Γ) (varT A ∪-set vart t)) x x₂) (is-prop-has-all-paths (is-prop-≗ (tgt-var Γ) (varT A ∪-set vart u)) x₁ x₃)
  has-all-paths-is-full Γ .(⇒ A t u) (side-cond₁ .Γ A t u ∂⁻ ∂⁺) (side-cond₂ .Γ .(⇒ A t u) full) = ⊥-elim (disjoint-cond Γ A t u ∂⁻ ∂⁺ full)
  has-all-paths-is-full Γ .(⇒ A t u) (side-cond₂ .Γ .(⇒ A t u) full) (side-cond₁ .Γ A t u ∂⁻ ∂⁺) = ⊥-elim (disjoint-cond Γ A t u ∂⁻ ∂⁺ full)
  has-all-paths-is-full Γ A (side-cond₂ .Γ .A x) (side-cond₂ .Γ .A x₁) = ap (side-cond₂ Γ A) (is-prop-has-all-paths (is-prop-≗ (varC (fst Γ)) (varT A)) x x₁)

  is-prop-full : ∀ Γ A → is-prop (A is-full-in Γ)
  is-prop-full Γ A = has-all-paths-is-prop (has-all-paths-is-full Γ A)




  eqdec-Ty : eqdec Ty
  eqdec-Tm : eqdec Tm
  eqdec-Sub : eqdec Sub

  eqdec-Ty ∗ ∗ = inl idp
  eqdec-Ty ∗ (⇒ _ _ _) = inr λ{()}
  eqdec-Ty (⇒ _ _ _) ∗ = inr λ{()}
  eqdec-Ty (⇒ A t u) (⇒ A' t' u') with eqdec-Ty A A' | eqdec-Tm t t' | eqdec-Tm u u'
  ...                                        | inl idp | inl idp | inl idp = inl idp
  ...                                        | inr A≠A' | _ | _ = inr λ {idp → A≠A' idp}
  ...                                        | inl idp | inr t≠t' | _ = inr λ p → t≠t' (snd (fst (=⇒Ty p)))
  ...                                        | inl idp | inl idp | inr u≠u' = inr λ p → u≠u' (snd (=⇒Ty p))
  eqdec-Tm (v x) (v y) with eqdecℕ x y
  ...                   | inl idp = inl idp
  ...                   | inr x≠y = inr λ{idp → x≠y idp}
  eqdec-Tm (v _) (coh _ _ _ _) = inr λ{()}
  eqdec-Tm (coh _ _ _ _) (v _) = inr λ{()}
  eqdec-Tm (coh Γ A Afull γ) (coh Γ' A' A'full γ') with eqdec-ps Γ Γ' | eqdec-Ty A A' | eqdec-Sub γ γ'
  ...                                               | inl idp | inl idp | inl idp = inl (ap (λ X → coh Γ A X γ) (is-prop-has-all-paths (is-prop-full Γ A) Afull A'full))
  ...                                               | inr Γ≠Γ' | _ | _ = inr λ {idp → Γ≠Γ' idp}
  ...                                               | inl idp | inr A≠A' | _ = inr λ p → A≠A' (snd (fst (coh= p)))
  ...                                               | inl idp | inl idp | inr γ≠γ' = inr λ p → γ≠γ' (snd (coh= p))
  eqdec-Sub <> <> = inl idp
  eqdec-Sub <> < _ , _ ↦ _ > = inr λ{()}
  eqdec-Sub < _ , _ ↦ _ > <> = inr λ{()}
  eqdec-Sub < γ , x ↦ t > < γ' , x' ↦ t' > with eqdec-Sub γ γ' | eqdecℕ x x' | eqdec-Tm t t'
  ...                                        | inl idp | inl idp | inl idp = inl idp
  ...                                        | inr γ≠γ' | _ | _ = inr λ {idp → γ≠γ' idp}
  ...                                        | inl idp | inr x≠x' | _ = inr λ p → x≠x' (snd (fst (<>= p)))
  ...                                        | inl idp | inl idp | inr t≠t' = inr λ p → t≠t' (snd (<>= p))
