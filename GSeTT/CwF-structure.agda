{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules

{- Categorical structure of the type theory for globular sets -}
module GSeTT.CwF-structure where

  {- cut-admissibility : action of substitutions preserves derivability -}
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)

  []T (ob Γ⊢) Δ⊢γ:Γ = ob (Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ)
  []T (ar Γ⊢A Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ = ar ([]T Γ⊢A Δ⊢γ:Γ) ([]t Γ⊢t:A Δ⊢γ:Γ) ([]t Γ⊢u:A Δ⊢γ:Γ)
  []t {Γ = (Γ ∙ _ # _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ _ idp) (inl x∈Γ)) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ _ _ idp) with (eqdecℕ x (ℓ Γ))
  ...                                                                                     | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  ...                                                                                     | inr _ = trT (wk[]T (Γ⊢t:A→Γ⊢A (var Γ⊢ x∈Γ)) Δ⊢γ+:Γ+ ^) ([]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ)
  []t {Γ = (Γ ∙ _ # _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ Γ⊢A idp) (inr (idp , idp))) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ x₁ Δ⊢t:A[γ] idp) with (eqdecℕ x (ℓ Γ))
  ...                                                                                     | inl _ = trT (wk[]T Γ⊢A Δ⊢γ+:Γ+ ^) Δ⊢t:A[γ]
  ...                                                                                     | inr x≠x = ⊥-elim (x≠x idp)


  {- action of identity on types and terms is trivial (true on syntax) -}
  [id]T : ∀ Γ A → (A [ Pre-id Γ ]Pre-Ty) == A
  [id]t : ∀ Γ t → (t [ Pre-id Γ ]Pre-Tm) == t

  [id]T Γ ∗ = idp
  [id]T Γ (t ⇒[ A ] u) = ⇒= ([id]T Γ A) ([id]t Γ t) ([id]t Γ u)
  [id]t ∅ (Var x) = idp
  [id]t (Γ ∙ y # B) (Var x) with (eqdecℕ x y)
  ...                              | inl x=y = Var= (x=y ^)
  ...                              | inr _ = [id]t Γ (Var x)


  {- identity is well-formed -}
  Γ⊢id:Γ : ∀ {Γ} → Γ ⊢C → Γ ⊢S Pre-id Γ > Γ
  Γ⊢id:Γ ec = es ec
  Γ⊢id:Γ Γ,x:A⊢@(cc Γ⊢ Γ⊢A idp) = sc (wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢) Γ,x:A⊢ (var Γ,x:A⊢ (inr (idp , [id]T _ _))) idp


  {- action of substitutions on types and terms respects composition -}
  [∘]T : ∀ {Γ Δ Θ A γ δ} → Γ ⊢T A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((A [ γ ]Pre-Ty) [ δ ]Pre-Ty) == (A [ γ ∘ δ ]Pre-Ty)
  [∘]t : ∀ {Γ Δ Θ A t γ δ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((t [ γ ]Pre-Tm) [ δ ]Pre-Tm) == (t [ γ ∘ δ ]Pre-Tm)

  [∘]T (ob _) _ _ = idp
  [∘]T (ar Γ⊢A Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ Θ⊢δ:Δ = ⇒= ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢t:A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢u:A Δ⊢γ:Γ Θ⊢δ:Δ)
  [∘]t (var {x = x} Γ⊢ x∈Γ) (sc {x = y} Δ⊢γ:Γ _ Δ⊢t:A[γ] idp) Θ⊢δ:Δ with (eqdecℕ x y )
  ... | inl idp = idp
  [∘]t (var Γ,y:A⊢ (inr (idp , idp))) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ] idp) Θ⊢δ:Δ | inr x≠x = ⊥-elim (x≠x idp)
  [∘]t (var (cc Γ⊢ _ _) (inl x∈Γ)) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ] idp) Θ⊢δ:Δ | inr _ = [∘]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ Θ⊢δ:Δ


  {- composition of well-formed substitutions is well-formed -}
  ∘-admissibility : ∀ {Γ Δ Θ γ δ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Θ ⊢S (γ ∘ δ) > Γ
  ∘-admissibility (es Δ⊢) Θ⊢δ:Δ = es (Δ⊢γ:Γ→Δ⊢ Θ⊢δ:Δ)
  ∘-admissibility (sc Δ⊢γ:Γ Γ,x:A⊢@(cc _ Γ⊢A _) Δ⊢t:A[γ] idp) Θ⊢δ:Δ = sc (∘-admissibility Δ⊢γ:Γ Θ⊢δ:Δ) Γ,x:A⊢ (trT ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([]t Δ⊢t:A[γ] Θ⊢δ:Δ)) idp

  {- composition is associative, this is true only for well-formed substitutions -}
  ∘-associativity : ∀ {Γ Δ Θ Ξ γ δ θ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Ξ ⊢S θ > Θ → ((γ ∘ δ) ∘ θ) == (γ ∘ (δ ∘ θ))
  ∘-associativity (es _) _ _ = idp
  ∘-associativity (sc Δ⊢γ:Γ _ Δ⊢t:A[γ] idp) Θ⊢δ:Δ Ξ⊢θ:Θ = ap² (λ σ  u → < σ , _ ↦ u >) (∘-associativity Δ⊢γ:Γ Θ⊢δ:Δ Ξ⊢θ:Θ) ([∘]t Δ⊢t:A[γ] Θ⊢δ:Δ Ξ⊢θ:Θ)


  {- Left unitality of composition -}

  -- To prove right-unitality, we need a analoguous of wk[]T and wk[]t for substitutions
  -- Composing if θ is a subst without x, acting (γ :: (x , u)) on it is same as acting just γ on it
  wk[]S : ∀ {Γ Δ γ x u B Θ θ} → Γ ⊢S θ > Θ → Δ ⊢S < γ , x ↦ u > > Γ ∙ x # B → (θ ∘ < γ , x ↦ u >) == (θ ∘ γ)
  wk[]S (es _) _ = idp
  wk[]S (sc Γ⊢θ:Θ _ Γ⊢t:A[θ] idp) Δ⊢γ+:Γ+ = ap² (λ σ  u → < σ , _ ↦ u >) (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+) (wk[]t Γ⊢t:A[θ] Δ⊢γ+:Γ+)

  ∘-left-unit : ∀{Γ Δ γ} → Δ ⊢S γ > Γ → (Pre-id Γ ∘ γ) == γ
  ∘-left-unit (es _) = idp
  ∘-left-unit Δ⊢γ+:Γ+@(sc {x = x} Δ⊢γ:Γ (cc Γ⊢ _ _) _ idp) with (eqdecℕ x x)
  ...                                                 | inl _ = ap (λ σ → < σ , _ ↦ _ >) (wk[]S (Γ⊢id:Γ Γ⊢) Δ⊢γ+:Γ+ >> ∘-left-unit Δ⊢γ:Γ)
  ...                                                 | inr x≠x = ⊥-elim (x≠x idp)

 {- Right unitality of composition (true on syntax)-}
  ∘-right-unit : ∀ {Δ γ} →  (γ ∘ Pre-id Δ) == γ
  ∘-right-unit {Δ} {<>} = idp
  ∘-right-unit {Δ} {< γ , y ↦ t >} = ap² (λ σ u → < σ , _ ↦ u >) ∘-right-unit ([id]t Δ t)

  {- Structure of CwF -}
  Γ,x:A⊢π:Γ : ∀ {Γ x A} → Γ ∙ x # A ⊢C → Γ ∙ x # A ⊢S Pre-π Γ x A > Γ
  Γ,x:A⊢π:Γ Γ,x:A⊢@(cc Γ⊢ _ _) = wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢

  -- TODO : complete the CwF structure
