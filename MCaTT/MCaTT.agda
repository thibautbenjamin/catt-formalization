{-# OPTIONS --without-K #-}

open import Prelude
import GSeTT.Syntax
import GSeTT.Rules
import GSeTT.Typed-Syntax
open import MCaTT.Desuspension
open import CaTT.Ps-contexts
import CaTT.CaTT

module MCaTT.MCaTT where

  J = CaTT.CaTT.J
  eqdecJ = CaTT.CaTT.eqdecJ

  open import Globular-TT.Syntax J

  ↓C : Pre-Ctx → Pre-Ctx
  ↓T : Pre-Ctx → Pre-Ty → Pre-Ty
  ↓t : Pre-Ctx → Pre-Tm → Pre-Tm
  ↓S : Pre-Ctx → Pre-Sub → Pre-Sub

  ↓C ⊘ = ⊘
  ↓C (Γ ∙ x # ∗) = ↓C Γ
  ↓C (Γ ∙ x # A@(_ ⇒[ _ ] _)) = (↓C Γ) ∙ x # (↓T Γ A)

  ↓T Γ ∗ = ∗
  ↓T Γ (t ⇒[ ∗ ] u) = ∗
  ↓T Γ (t ⇒[ A@(_ ⇒[ _ ] _) ] u) = (↓t Γ t) ⇒[ ↓T Γ A ] (↓t Γ u)

  count-objects-in_until_ : Pre-Ctx → ℕ → ℕ
  count-objects-in ⊘ until x = 0
  count-objects-in Γ ∙ y # ∗ until x with dec-≤ y x
  ... | inl y≤x = S (count-objects-in Γ until x)
  ... | inr x<y = count-objects-in Γ until x
  count-objects-in Γ ∙ y # (_ ⇒[ _ ] _) until x = count-objects-in Γ until x

  ↓t Γ (Var x) = Var (x - (count-objects-in Γ until x))
  ↓t Δ (Tm-constructor i@(((Γ , _) , _) , _) γ) = Tm-constructor i (↓S (GPre-Ctx Γ) γ)

  ↓S Γ <> = <>
  ↓S Γ < γ , x ↦ t > = < ↓S Γ γ , x ↦ ↓t Γ t >

  rule : J → GSeTT.Typed-Syntax.Ctx × Pre-Ty
  rule (((Γ , Γ⊢ps) , A) , _) =
    let Γ⊢ = Γ⊢ps→Γ⊢ Γ⊢ps in
    (↓GC Γ Γ⊢ , ↓⊢C Γ Γ⊢) , ↓T (GPre-Ctx Γ) (CaTT.CaTT.Ty→Pre-Ty A)

  open import Globular-TT.Rules J rule
  open import Globular-TT.CwF-Structure J rule
  open import Globular-TT.Uniqueness-Derivations J rule eqdecJ
  open import Globular-TT.Disks J rule eqdecJ
