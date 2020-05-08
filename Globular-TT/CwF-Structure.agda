{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax

{- Structure of CwF of a globular type theory : Cut admissibility is significantly harder and has to be proved together with it -}
module Globular-TT.CwF-Structure (index : Set) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index)) where
  open import Globular-TT.Syntax index
  open import Globular-TT.Rules index rule

  A∈Γ→Γ⊢A : ∀ {Γ x A} →  Γ ⊢C → x # A ∈ Γ → Γ ⊢T A
  A∈Γ→Γ⊢A Γ+⊢@(cc Γ⊢ Γ⊢B) (inl A∈Γ) = wkT (A∈Γ→Γ⊢A Γ⊢ A∈Γ) Γ+⊢
  A∈Γ→Γ⊢A Γ+⊢@(cc Γ⊢ Γ⊢A) (inr (idp , idp)) = wkT Γ⊢A Γ+⊢

  {- cut-admissibility -}
  -- notational shortcut : if A = B a term of type A is also of type B
  trT : ∀ {Γ A B t} → A == B → Γ ⊢t t # A → Γ ⊢t t # B
  trT idp Γ⊢t:A = Γ⊢t:A

  {- action on weakened types and terms -}
  n∉Γ : ∀ {Γ A n} → Γ ⊢C → (C-length Γ ≤ n) → ¬ (n # A ∈ Γ)
  n∉Γ (cc Γ⊢ _) l+1≤n (inl n∈Γ) = n∉Γ Γ⊢ (Sn≤m→n≤m l+1≤n) n∈Γ
  n∉Γ (cc Γ⊢ _) Sn≤n (inr (idp , idp)) = Sn≰n _ Sn≤n

  lΓ∉Γ : ∀ {Γ A} → Γ ⊢C → ¬ ((C-length Γ) # A ∈ Γ)
  lΓ∉Γ Γ⊢ = n∉Γ Γ⊢ (n≤n _)

  wk[]T : ∀ {Γ Δ γ x u A B} → Γ ⊢T A → Δ ⊢S < γ , x ↦ u > > (Γ ∙ x # B) → (A [ < γ , x ↦ u > ]Pre-Ty) == (A [ γ ]Pre-Ty)
  wk[]t : ∀ {Γ Δ γ x u A t B} → Γ ⊢t t # A → Δ ⊢S < γ , x ↦ u > > (Γ ∙ x # B) → (t [ < γ , x ↦ u > ]Pre-Tm) == (t [ γ ]Pre-Tm)
  wk[]S : ∀ {Γ Δ γ x u B Θ θ} → Γ ⊢S θ > Θ → Δ ⊢S < γ , x ↦ u > > (Γ ∙ x # B) → (θ ∘ < γ , x ↦ u >) == (θ ∘ γ)
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)
  [∘]T : ∀ {Γ Δ Θ A γ δ} → Γ ⊢T A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((A [ γ ]Pre-Ty) [ δ ]Pre-Ty) == (A [ γ ∘ δ ]Pre-Ty)
  [∘]t : ∀ {Γ Δ Θ A t γ δ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → ((t [ γ ]Pre-Tm) [ δ ]Pre-Tm) == (t [ γ ∘ δ ]Pre-Tm)
  ∘-admissibility : ∀ {Γ Δ Θ γ δ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Θ ⊢S (γ ∘ δ) > Γ
  ∘-associativity : ∀ {Γ Δ Θ Ξ γ δ θ} → Δ ⊢S γ > Γ → Θ ⊢S δ > Δ → Ξ ⊢S θ > Θ → ((γ ∘ δ) ∘ θ) == (γ ∘ (δ ∘ θ))

  wk[]T (ob Γ⊢) _ = idp
  wk[]T (ar Γ⊢A Γ⊢t:A Γ⊢u:A) Δ⊢γ+:Γ+ = ⇒= (wk[]T Γ⊢A Δ⊢γ+:Γ+) (wk[]t Γ⊢t:A Δ⊢γ+:Γ+) (wk[]t Γ⊢u:A Δ⊢γ+:Γ+)
  wk[]t {x = x} (var {x = y} Γ⊢ y∈Γ) Δ⊢γ+:Γ+             with (eqdecℕ y x)
  ...                                                    | inr _ = idp
  wk[]t (var Γ⊢ l∈Γ) (sc Δ⊢γ:Γ (cc _ _) _) | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ l∈Γ)
  wk[]t (tm i _ Γ⊢θ:Θ) Δ⊢γ+:Γ+ = Tm-constructor= idp (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+)
  wk[]S (es _) _ = idp
  wk[]S (sc Γ⊢θ:Θ _ Γ⊢t:A[θ]) Δ⊢γ+:Γ+ = <,>= (wk[]S Γ⊢θ:Θ Δ⊢γ+:Γ+) idp (wk[]t Γ⊢t:A[θ] Δ⊢γ+:Γ+)


  []T (ob Γ⊢) Δ⊢γ:Γ = ob (Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ)
  []T (ar Γ⊢A Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ = ar ([]T Γ⊢A Δ⊢γ:Γ) ([]t Γ⊢t:A Δ⊢γ:Γ) ([]t Γ⊢u:A Δ⊢γ:Γ)
  []t {t = .(Tm-constructor i _)} (tm i Ci⊢Ti x) Δ⊢γ:Γ = trT ([∘]T Ci⊢Ti x Δ⊢γ:Γ ^) (tm i Ci⊢Ti (∘-admissibility x Δ⊢γ:Γ))
  []t {Γ = (Γ ∙ _ # _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ _) (inl x∈Γ)) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ _ _) with (eqdecℕ x (C-length Γ))
  ...                                                                                     | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  ...                                                                                     | inr _ = trT (wk[]T (A∈Γ→Γ⊢A Γ⊢ x∈Γ) Δ⊢γ+:Γ+ ^) ([]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ)
  []t {Γ = (Γ ∙ _ # _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ Γ⊢A) (inr (idp , idp))) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ x₁ Δ⊢t:A[γ]) with (eqdecℕ x (C-length Γ))
  ...                                                                                     | inl idp = trT (wk[]T Γ⊢A Δ⊢γ+:Γ+ ^) Δ⊢t:A[γ]
  ...                                                                                     | inr x≠x = ⊥-elim (x≠x idp)


  [∘]T (ob _) _ _ = idp
  [∘]T (ar Γ⊢A Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ Θ⊢δ:Δ = ⇒= ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢t:A Δ⊢γ:Γ Θ⊢δ:Δ) ([∘]t Γ⊢u:A Δ⊢γ:Γ Θ⊢δ:Δ)
  [∘]t (tm i Ci⊢Ti x) Δ⊢γ:Γ Θ⊢δ:Δ = Tm-constructor= idp (∘-associativity x Δ⊢γ:Γ Θ⊢δ:Δ )
  [∘]t (var {x = x} Γ,y:A⊢ x∈Γ+) (sc {x = y} Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ with (eqdecℕ x y )
  ...                                                                | inl idp = idp
  [∘]t (var Γ,y:A⊢ (inr (idp , idp))) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr x≠x = ⊥-elim (x≠x idp)
  [∘]t (var (cc Γ⊢ _) (inl x∈Γ)) (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ | inr _ = [∘]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ Θ⊢δ:Δ

  ∘-admissibility (es Δ⊢) Θ⊢δ:Δ = es (Δ⊢γ:Γ→Δ⊢ Θ⊢δ:Δ)
  ∘-admissibility (sc Δ⊢γ:Γ Γ,x:A⊢@(cc _ Γ⊢A) Δ⊢t:A[γ]) Θ⊢δ:Δ = sc (∘-admissibility Δ⊢γ:Γ Θ⊢δ:Δ) Γ,x:A⊢ (trT ([∘]T Γ⊢A Δ⊢γ:Γ Θ⊢δ:Δ) ([]t Δ⊢t:A[γ] Θ⊢δ:Δ))

  ∘-associativity (es _) _ _ = idp
  ∘-associativity (sc Δ⊢γ:Γ _ Δ⊢t:A[γ]) Θ⊢δ:Δ Ξ⊢θ:Θ = <,>= (∘-associativity Δ⊢γ:Γ Θ⊢δ:Δ Ξ⊢θ:Θ) idp ([∘]t Δ⊢t:A[γ] Θ⊢δ:Δ Ξ⊢θ:Θ)

  Γ⊢t:A→Γ⊢A : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢T A
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc Γ⊢ Γ⊢A) (inl y∈Γ)) = wkT (Γ⊢t:A→Γ⊢A (var Γ⊢ y∈Γ)) Γ,x:A⊢
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc _ _) (inr (idp , idp))) = Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢
  Γ⊢t:A→Γ⊢A (tm i Ci⊢Ti Γ⊢γ:Δ) = []T Ci⊢Ti Γ⊢γ:Δ

  {- action of identity on types terms and substitutions is trivial (true on syntax) -}
  [id]T : ∀ Γ A → (A [ Pre-id Γ ]Pre-Ty) == A
  [id]t : ∀ Γ t → (t [ Pre-id Γ ]Pre-Tm) == t
  ∘-right-unit : ∀ {Δ γ} →  (γ ∘ Pre-id Δ) == γ

  [id]T Γ ∗ = idp
  [id]T Γ (⇒ A t u) = ⇒= ([id]T Γ A) ([id]t Γ t) ([id]t Γ u)
  [id]t Γ (Tm-constructor i γ) = Tm-constructor= idp ∘-right-unit
  [id]t ⊘ (Var x) = idp
  [id]t (Γ ∙ y # B) (Var x) with (eqdecℕ x y)
  ...                              | inl x=y = Var= (x=y ^)
  ...                              | inr _ = [id]t Γ (Var x)
  ∘-right-unit {Δ} {<>} = idp
  ∘-right-unit {Δ} {< γ , y ↦ t >} = <,>= ∘-right-unit idp ([id]t Δ t) -- ::= ∘-right-unit (×= idp ([id]t Δ t))

  {- identity is well-formed -}
  Γ⊢id:Γ : ∀ {Γ} → Γ ⊢C → Γ ⊢S Pre-id Γ > Γ
  Γ⊢id:Γ ec = es ec
  Γ⊢id:Γ Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = sc (wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢) Γ,x:A⊢ (var Γ,x:A⊢ (inr (idp , [id]T _ _)))



  {- composition is associative -}

  ∘-left-unit : ∀{Γ Δ γ} → Δ ⊢S γ > Γ → (Pre-id Γ ∘ γ) == γ
  ∘-left-unit (es _) = idp
  ∘-left-unit Δ⊢γ+:Γ+@(sc {x = x} Δ⊢γ:Γ (cc Γ⊢ _) _) with (eqdecℕ x x)
  ...                                                  | inl idp = <,>= (wk[]S (Γ⊢id:Γ Γ⊢) Δ⊢γ+:Γ+ >> ∘-left-unit Δ⊢γ:Γ) idp idp
  ...                                                  | inr x≠x = ⊥-elim (x≠x idp)


  {- Structure of CwF -}

  Γ,x:A⊢π:Γ : ∀ {Γ x A} → (Γ ∙ x # A) ⊢C → (Γ ∙ x # A) ⊢S Pre-π Γ x A > Γ
  Γ,x:A⊢π:Γ Γ,x:A⊢@(cc Γ⊢ _) = wkS (Γ⊢id:Γ Γ⊢) Γ,x:A⊢
  -- TODO : finish

