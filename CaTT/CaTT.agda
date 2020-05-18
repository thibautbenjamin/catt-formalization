{-# OPTIONS --rewriting #-}

open import Prelude
open import CaTT.Ps-contexts
open import CaTT.Fullness
import GSeTT.Typed-Syntax


module CaTT.CaTT where
   J : Set₁
   J = Σ (ps-ctx × Ty) λ {(Γ , A) → A is-full-in Γ }

   open import Globular-TT.Syntax J

   Ty→Pre-Ty : Ty → Pre-Ty
   Tm→Pre-Tm : Tm → Pre-Tm
   Sub→Pre-Sub : Sub → Pre-Sub

   Ty→Pre-Ty ∗ = ∗
   Ty→Pre-Ty (⇒ A t u) = ⇒ (Ty→Pre-Ty A) (Tm→Pre-Tm t) (Tm→Pre-Tm u)

   Tm→Pre-Tm (v x) = Var x
   Tm→Pre-Tm (coh Γ A Afull γ) = Tm-constructor (((Γ , A)) , Afull) (Sub→Pre-Sub γ)

   Sub→Pre-Sub <> = <>
   Sub→Pre-Sub < γ , x ↦ t > = < Sub→Pre-Sub γ , x ↦ Tm→Pre-Tm t >

   rule : J → GSeTT.Typed-Syntax.Ctx × Pre-Ty
   rule ((Γ , A) , _) = (fst Γ , Γ⊢ps→Γ⊢ (snd Γ)) , Ty→Pre-Ty A

   open import Globular-TT.Rules J rule
   open import Globular-TT.CwF-Structure J rule
   open import Globular-TT.Disks J rule
   open import Globular-TT.Uniqueness-Derivations J rule

   well-foundedness : well-founded
   well-foundedness ((Γ , A) , Afull) Γ⊢A = {!!}

   eqdecJ : eqdec J
   eqdecJ ((Γ , A) , Afull) ((Γ' , A') , A'full) with eqdec-ps Γ Γ' | eqdec-Ty A A'
   ...                                           | inl idp | inl idp = inl (ap (λ X → ((Γ , A) , X)) (is-prop-has-all-paths (is-prop-full Γ A) Afull A'full))
   ...                                           | inr Γ≠Γ' | _ = inr λ{idp → Γ≠Γ' idp}
   ...                                           | inl idp | inr A≠A' = inr λ{idp → A≠A' idp}


   open import Globular-TT.Dec-Type-Checking J rule well-foundedness eqdecJ
