{-# OPTIONS --rewriting --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Uniqueness-Derivations
open import Sets ℕ eqdecℕ
open import GSeTT.Dec-Type-Checking
open import CaTT.Ps-contexts
open import CaTT.Relation

{- PS-contexts -}
module CaTT.Uniqueness-Derivations-Ps where
  Γ⊢psx-dim≤ : ∀ {Γ x A} → Γ ⊢ps x # A → dim A ≤ dimC Γ
  Γ⊢psx-dim≤  pss = n≤n 0
  Γ⊢psx-dim≤ (psd Γ⊢psy) = Sn≤m→n≤m (Γ⊢psx-dim≤ Γ⊢psy)
  Γ⊢psx-dim≤ {((Γ :: (_ , A)) :: (_ , _))} {_} {_} (pse Γ⊢psx idp idp idp idp idp) with dec-≤ (dimC (Γ :: (length Γ , A))) (S (dim A))
  ... | inr res = Sn≤m→n≤m (≰ res)
  ... | inl res = n≤n (S (dim A))

  Γ⊢psx-dim : ∀ {Γ x y A B} → Γ ⊢ps x # A → Γ ⊢ps y # B → dim A == dim B → x == y
  Γ⊢psx-dim pss pss dimA=dimB = idp
  Γ⊢psx-dim {x = x} {y = y} {A = A} {B = B} (psd {x = x₁} Γ⊢psx) (psd {x = x₂} Γ⊢psy) dimA=dimB  = =Var (tgt= (unique-type (Γ⊢psx:A→Γ⊢x:A Γ⊢psx) (Γ⊢psx:A→Γ⊢x:A Γ⊢psy) (ap Var (Γ⊢psx-dim Γ⊢psx Γ⊢psy (ap S dimA=dimB)))))
  Γ⊢psx-dim {B = ∗} pss (psd Γ⊢psy) dimA=dimB = ⊥-elim (Sn≰n _ ((Γ⊢psx-dim≤ Γ⊢psy)))
  Γ⊢psx-dim {A = ∗} (psd Γ⊢psx) pss dimA=dimB = ⊥-elim (Sn≰n _ ((Γ⊢psx-dim≤ Γ⊢psx)))
  Γ⊢psx-dim (pse _ _ _ _ idp idp) (pse _ _ _ _ idp idp) dimA==dimB = idp
  Γ⊢psx-dim Γ++⊢psx@(psd Γ++⊢_) Γ++⊢psy@(pse _ idp idp idp idp idp) dimA=dimB with psx-◃-linear→ Γ++⊢psx _ _ (Γ⊢x:A→x∈Γ (psvar Γ++⊢psx)) (Γ⊢x:A→x∈Γ (psvar Γ++⊢psy))
  ... | inl (inl x◃Sl) = ⊥-elim (Sn≰n-t (dimA=dimB ^) (⟿dim (psvar Γ++⊢psx) (psvar Γ++⊢psy) (⊢psx-◃→⟿ Γ++⊢psx x◃Sl)))
  ... | inl (inr Sl◃x) = ⊥-elim (Sn≰n-t (dimA=dimB) (⟿dim (psvar Γ++⊢psy) (psvar Γ++⊢psx) (⊢psx-◃→⟿ Γ++⊢psy Sl◃x)))
  ... | inr idp = idp
  Γ⊢psx-dim Γ++⊢psx@(pse _  idp idp idp idp idp) Γ++⊢psy@(psd _) dimA=dimB with psx-◃-linear→ Γ++⊢psx _ _ (Γ⊢x:A→x∈Γ (psvar Γ++⊢psx)) (Γ⊢x:A→x∈Γ (psvar Γ++⊢psy))
  ... | inl (inl Sl◃y) = ⊥-elim (Sn≰n-t (dimA=dimB ^) (⟿dim (psvar Γ++⊢psx) (psvar Γ++⊢psy) (⊢psx-◃→⟿ Γ++⊢psx Sl◃y)))
  ... | inl (inr y◃Sl) = ⊥-elim (Sn≰n-t (dimA=dimB) (⟿dim (psvar Γ++⊢psy) (psvar Γ++⊢psx) (⊢psx-◃→⟿ Γ++⊢psy y◃Sl)))
  ... | inr idp = idp


  has-all-paths-⊢psx : ∀ {Γ x A} → has-all-paths (Γ ⊢ps x # A)
  has-all-paths-⊢psx pss pss = idp
  has-all-paths-⊢psx (psd a) (psd b) with (Γ⊢psx-dim a b idp)
  ... | idp with unique-type (psvar a) (psvar b) idp
  ... | p = psd↓ a b (=Var (snd (fst (=⇒ p)))) (has-all-paths-⊢psx _ _)
  has-all-paths-⊢psx  pss (psd b) with (psvar b)
  ... | var _ (inl ())
  ... | var _ (inr ())
  has-all-paths-⊢psx (psd a) pss with (psvar a)
  ... | var _ (inl ())
  ... | var _ (inr ())
  has-all-paths-⊢psx (psd a) (pse b idp idp idp idp idp) with (psvar a)
  ... | var _ (inl (inl contra)) = ⊥-elim (l∉ (psv b) (n≤Sn _) (Γ⊢x:A→x∈Γ (Γ⊢tgt (Γ⊢t:A→Γ⊢A (var (psv b) contra)))))
  has-all-paths-⊢psx (pse a idp idp idp idp idp) (psd b) with psvar b
  ... | var _ (inl (inl contra)) = ⊥-elim (l∉ (psv a) (n≤Sn _) (Γ⊢x:A→x∈Γ (Γ⊢tgt (Γ⊢t:A→Γ⊢A (var (psv a) contra)))))
  has-all-paths-⊢psx (pse a idp idp idp idp idp) (pse b p q r s u) = let eq = =Var (snd (fst (=⇒ r))) in pse↓ a _ _ _ _ _ b _ _ _ _ _ eq (has-all-paths-⊢psx _ _)

  has-all-paths-⊢ps : ∀ Γ → has-all-paths (Γ ⊢ps)
  has-all-paths-⊢ps Γ (ps Γ⊢psx₁) (ps Γ⊢psx₂) = ps↓ Γ⊢psx₁ Γ⊢psx₂ (Γ⊢psx-dim Γ⊢psx₁ Γ⊢psx₂ idp) (has-all-paths-⊢psx _ _)

  is-prop-⊢ps : ∀ Γ → is-prop (Γ ⊢ps)
  is-prop-⊢ps Γ = has-all-paths-is-prop (has-all-paths-⊢ps Γ)

  eqdec-ps : eqdec ps-ctx
  eqdec-ps (Γ , Γ⊢ps) (Δ , Δ⊢ps) with eqdec-PreCtx Γ Δ
  ... | inl idp = inl (Σ= idp (is-prop-has-all-paths (is-prop-⊢ps Γ) _ _))
  ... | inr Γ≠Δ = inr λ{idp → Γ≠Δ idp}


