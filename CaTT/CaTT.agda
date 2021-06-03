{-# OPTIONS #-}

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

   open GSeTT.Typed-Syntax
   open import Sets ℕ eqdecℕ

   open import Globular-TT.Rules J rule
   open import Globular-TT.CwF-Structure J rule
   open import Globular-TT.Disks J rule
   open import Globular-TT.Uniqueness-Derivations J rule

   dim-tm : ∀ {Γ x A} → Γ ⊢t Var x # A → ℕ
   dim-tm {Γ} {x} {A} _ = dim A

   ∈-set-∪ : ∀ {x} A B → x ∈-set (A ∪-set B) → (x ∈-set A) + (x ∈-set B)
   ∈-set-∪ = {!!}

   ∈-singleton : ∀ {x y} → y ∈-set singleton x → y == x
   ∈-singleton = {!!}

   dim-∈-var : ∀ {Γ A x B} → Γ ⊢t Var x # B → Γ ⊢T (Ty→Pre-Ty A) → x ∈-set varT A → dim B < dim (Ty→Pre-Ty A)
   dim-∈-var-t : ∀ {Γ t A x B} → Γ ⊢t Var x # B → Γ ⊢t (Tm→Pre-Tm t) # (Ty→Pre-Ty A) → x ∈-set vart t → dim B ≤ dim (Ty→Pre-Ty A)

   dim-∈-var {Γ} {A⇒@(⇒ A t u)} {x} {B} Γ⊢x (ar Γ⊢A Γ⊢t Γ⊢u) x∈A⇒ with ∈-set-∪ (varT A) (vart t ∪-set vart u) x∈A⇒
   ... | inl x∈A = n≤m→n≤Sm (dim-∈-var Γ⊢x Γ⊢A x∈A)
   ... | inr x∈t∪u with ∈-set-∪ (vart t) (vart u) x∈t∪u
   ... | inl x∈t = S≤ (dim-∈-var-t Γ⊢x Γ⊢t x∈t)
   ... | inr x∈u = S≤ (dim-∈-var-t Γ⊢x Γ⊢u x∈u)

   dim-∈-var-t {t = v x} Γ⊢x Γ⊢t x∈t with unique-type Γ⊢x Γ⊢t (ap Var (∈-singleton x∈t))
   ... | idp = n≤n _
   dim-∈-var-t {t = coh Γ A x γ} Γ⊢x Γ⊢t x∈t = {!!}

   -- techincal : a full term contains a variable of dimension at least one minus the dimension of the context
   full-term-have-max-variables : ∀ {Γ A Γ⊢ps} → A is-full-in ((Γ , Γ⊢ps)) →
     Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-set varT A) × (dimC (GPre-Ctx Γ) ≤ S (dim-tm Γ⊢x))})
   full-term-have-max-variables = {!!}

   well-foundedness : well-founded
   well-foundedness ((Γ , A) , Afull) Γ⊢A with full-term-have-max-variables Afull
   ... |((x , B) , Γ⊢x) , (x∈Γ , dimΓ≤Sdimx) = ≤T dimΓ≤Sdimx (dim-∈-var Γ⊢x Γ⊢A x∈Γ)

   eqdecJ : eqdec J
   eqdecJ ((Γ , A) , Afull) ((Γ' , A') , A'full) with eqdec-ps Γ Γ' | eqdec-Ty A A'
   ...                                           | inl idp | inl idp = inl (ap (λ X → ((Γ , A) , X)) (is-prop-has-all-paths (is-prop-full Γ A) Afull A'full))
   ...                                           | inr Γ≠Γ' | _ = inr λ{idp → Γ≠Γ' idp}
   ...                                           | inl idp | inr A≠A' = inr λ{idp → A≠A' idp}



   open import Globular-TT.Dec-Type-Checking J rule well-foundedness eqdecJ
