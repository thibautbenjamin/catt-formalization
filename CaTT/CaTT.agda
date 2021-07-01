{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude
import GSeTT.Syntax
import GSeTT.Rules
open import CaTT.Ps-contexts
open import CaTT.Relation
open import CaTT.Uniqueness-Derivations-Ps
open import CaTT.Decidability-ps
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

   eqdecJ : eqdec J
   eqdecJ ((Γ , A) , Afull) ((Γ' , A') , A'full) with eqdec-ps Γ Γ' | CaTT.Fullness.eqdec-Ty A A'
   ...                                           | inl idp | inl idp = inl (ap (λ X → ((Γ , A) , X)) (is-prop-has-all-paths (is-prop-full Γ A) Afull A'full))
   ...                                           | inr Γ≠Γ' | _ = inr λ{idp → Γ≠Γ' idp}
   ...                                           | inl idp | inr A≠A' = inr λ{idp → A≠A' idp}

   open import Globular-TT.Uniqueness-Derivations J rule eqdecJ
   open import Globular-TT.Disks J rule eqdecJ


   dim-tm : ∀ {Γ x A} → Γ ⊢t Var x # A → ℕ
   dim-tm {Γ} {x} {A} _ = dim A

   dim-∈-var : ∀ {Γ A x B} → Γ ⊢t Var x # B → Γ ⊢T (Ty→Pre-Ty A) → x ∈-set varT A → dim B < dim (Ty→Pre-Ty A)
   dim-∈-var-t : ∀ {Γ t A x B} → Γ ⊢t Var x # B → Γ ⊢t (Tm→Pre-Tm t) # (Ty→Pre-Ty A) → x ∈-set vart t → dim B ≤ dim (Ty→Pre-Ty A)

   dim-∈-var {Γ} {A⇒@(⇒ A t u)} {x} {B} Γ⊢x (ar Γ⊢A Γ⊢t Γ⊢u) x∈A⇒ with ∈-∪ {varT A} {vart t ∪-set vart u} x∈A⇒
   ... | inl x∈A = n≤m→n≤Sm (dim-∈-var Γ⊢x Γ⊢A x∈A)
   ... | inr x∈t∪u with ∈-∪ {vart t} {vart u} x∈t∪u
   ... | inl x∈t = S≤ (dim-∈-var-t Γ⊢x Γ⊢t x∈t)
   ... | inr x∈u = S≤ (dim-∈-var-t Γ⊢x Γ⊢u x∈u)
   dim-∈-var-t {t = v x} Γ⊢x Γ⊢t (inr idp) with unique-type Γ⊢x Γ⊢t (ap Var idp)
   ... | idp = n≤n _
   dim-∈-var-t {t = coh Γ A Afull γ} Γ⊢x (tm Γ⊢A Δ⊢γ:Γ p) x∈t = {!!}

   GdimT : ∀ {A} → GSeTT.Syntax.dim A == dim (GPre-Ty A)
   GdimT {GSeTT.Syntax.∗} = idp
   GdimT {GSeTT.Syntax.⇒ A _ _} = ap S GdimT

   GdimC : ∀ {Γ} → GSeTT.Syntax.dimC Γ == dimC (GPre-Ctx Γ)
   GdimC {nil} = idp
   GdimC {Γ :: (x , A)} = ap² max (GdimC {Γ}) GdimT

   G#∈ : ∀ {Γ x A} → x GSeTT.Syntax.# A ∈ Γ → x # (GPre-Ty A) ∈ (GPre-Ctx Γ)
   G#∈ {Γ :: a} (inl x∈Γ) = inl (G#∈ x∈Γ)
   G#∈ {Γ :: a} (inr (idp , idp)) = inr (idp , idp)

   G∈ : ∀ {Γ x} → x GSeTT.Syntax.∈ Γ → x ∈-set (varC Γ)
   G∈ {Γ :: (a , _)} (inl x∈Γ) = ∈-∪₁ {A = varC Γ} {B = singleton a} (G∈ x∈Γ)
   G∈ {Γ :: (x , _)} (inr idp) = ∈-∪₂ {A = varC Γ} {B = singleton x} (∈-singleton x)

   private
     every-term-has-variables : ∀ {Γ t A} → Γ ⊢t (Tm→Pre-Tm t) # A → Σ ℕ λ x → x ∈-set vart t
     every-term-has-variables {Γ} {v x} {A} Γ⊢t = x , ∈-singleton x
     every-term-has-variables {Γ} {coh (nil , (ps Δ⊢ps)) _ _ γ} {A} (tm _ Γ⊢γ idp) = ⊥-elim (∅-is-not-ps _ _ Δ⊢ps)
     every-term-has-variables {Γ} {coh ((_ :: _) , Δ⊢ps) _ _ <>} {A} (tm _ () idp)
     every-term-has-variables {Γ} {coh ((_ :: _) , Δ⊢ps) _ _ < γ , _ ↦ u >} {A} (tm _ (sc _ _ Γ⊢u _) idp) with every-term-has-variables Γ⊢u
     ... | (x , x∈) = x , ∈-∪₂ {A = varS γ} {B = vart u} x∈


   side-cond₁-not𝔻0 : ∀ Γ Γ⊢ps A t → (GPre-Ctx Γ) ⊢t (Tm→Pre-Tm t) # (Ty→Pre-Ty A) → ((varT A) ∪-set (vart t)) ⊂ (src-var (Γ , Γ⊢ps)) → Γ ≠ (nil :: (0 , GSeTT.Syntax.∗))
   side-cond₁-not𝔻0 .(nil :: (0 , GSeTT.Syntax.∗)) (ps pss) A t Γ⊢t incl idp with every-term-has-variables Γ⊢t | dec-≤ 0 0
   ... | x , x∈A | inl _ = incl _ (∈-∪₂ {A = varT A} {B = vart t} x∈A)
   ... | x , x∈A | inr _ = incl _ (∈-∪₂ {A = varT A} {B = vart t} x∈A)
   side-cond₁-not𝔻0 .(nil :: (0 , GSeTT.Syntax.∗)) (ps (psd Γ⊢psf)) A t Γ⊢t incl idp = ⇒≠∗ (𝔻0-type _ _ (psvar Γ⊢psf))

   max-srcᵢ-var-def : ∀ {Γ x A i} → (Γ⊢psx : Γ ⊢ps x # A) → 0 < i → ℕ × Pre-Ty
   max-srcᵢ-var-def pss _ = 0 , ∗
   max-srcᵢ-var-def (psd Γ⊢psx) 0<i = max-srcᵢ-var-def Γ⊢psx 0<i
   max-srcᵢ-var-def {_} {x} {A} {i} (pse Γ⊢psx idp idp idp idp idp) 0<i  with dec-≤ i (GSeTT.Syntax.dim A)
   ... | inl i≤dA = max-srcᵢ-var-def Γ⊢psx 0<i
   ... | inr dA<i with dec-≤ (GSeTT.Syntax.dim A) (dim (snd (max-srcᵢ-var-def Γ⊢psx 0<i)))
   ... | inl _ = max-srcᵢ-var-def Γ⊢psx 0<i
   ... | inr _ = x , GPre-Ty A

   max-srcᵢ-var-∈ : ∀ {Γ x A i} → (Γ⊢psx : Γ ⊢ps x # A) → (0<i : 0 < i) → fst (max-srcᵢ-var-def Γ⊢psx 0<i) ∈-list (srcᵢ-var i Γ⊢psx)
   max-srcᵢ-var-∈ pss 0<i = transport {B = 0 ∈-list_} (simplify-if 0<i ^) (inr idp)
   max-srcᵢ-var-∈ (psd Γ⊢psx) 0<i = max-srcᵢ-var-∈ Γ⊢psx 0<i
   max-srcᵢ-var-∈ {Γ} {x} {A} {i} (pse Γ⊢psx idp idp idp idp idp) 0<i with dec-≤ i (GSeTT.Syntax.dim A)
   ... | inl _ = max-srcᵢ-var-∈ Γ⊢psx 0<i
   ... | inr _  with dec-≤ (GSeTT.Syntax.dim A) (dim (snd (max-srcᵢ-var-def Γ⊢psx 0<i)))
   ... | inl _ = inl (inl (max-srcᵢ-var-∈ Γ⊢psx 0<i))
   ... | inr _ = inr idp

   max-srcᵢ-var-⊢ : ∀ {Γ x A i} → (Γ⊢psx : Γ ⊢ps x # A) → (0<i : 0 < i) → GPre-Ctx Γ ⊢t Var (fst (max-srcᵢ-var-def Γ⊢psx 0<i)) # snd (max-srcᵢ-var-def Γ⊢psx 0<i)
   max-srcᵢ-var-⊢ pss 0<i = var (cc ec (ob ec) idp) (inr (idp , idp))
   max-srcᵢ-var-⊢ (psd Γ⊢psx) 0<i = max-srcᵢ-var-⊢ Γ⊢psx 0<i
   max-srcᵢ-var-⊢ {Γ} {x} {A} {i} Γ+⊢ps@(pse Γ⊢psx idp idp idp idp idp) 0<i with dec-≤ i (GSeTT.Syntax.dim A)
   ... | inl _ = wkt (wkt (max-srcᵢ-var-⊢ Γ⊢psx 0<i) ((GCtx _ (GSeTT.Rules.Γ,x:A⊢→Γ⊢ (psv Γ+⊢ps))))) (GCtx _ (psv Γ+⊢ps))
   ... | inr _  with dec-≤ (GSeTT.Syntax.dim A) (dim (snd (max-srcᵢ-var-def Γ⊢psx 0<i)))
   ... | inl _ = wkt (wkt (max-srcᵢ-var-⊢ Γ⊢psx 0<i) ((GCtx _ (GSeTT.Rules.Γ,x:A⊢→Γ⊢ (psv Γ+⊢ps))))) (GCtx _ (psv Γ+⊢ps))
   ... | inr _ = var (GCtx _ (psv Γ+⊢ps)) (inr (idp , idp))


   max-srcᵢ-var-dim : ∀ {Γ x A i} → (Γ⊢psx : Γ ⊢ps x # A) → (0<i : 0 < i) →  min i (S (dimC (GPre-Ctx Γ))) == S (dim (snd (max-srcᵢ-var-def Γ⊢psx 0<i)))
   max-srcᵢ-var-dim pss 0<i = simplify-min-r 0<i
   max-srcᵢ-var-dim (psd Γ⊢psx) 0<i = max-srcᵢ-var-dim Γ⊢psx 0<i
   max-srcᵢ-var-dim {Γ} {x} {A} {i} (pse {Γ = Δ} Γ⊢psx idp idp idp idp idp) 0<i with dec-≤ i (GSeTT.Syntax.dim A)
   ... | inl i≤dA = simplify-min-l (n≤m→n≤Sm (≤T (≤-= i≤dA (GdimT {A})) (m≤max (max (dimC (GPre-Ctx Δ)) _) (dim (GPre-Ty A))) )) >> (simplify-min-l (≤T i≤dA (≤-= (S≤ (dim-dangling Γ⊢psx)) (ap S (GdimC {Δ})))) ^) >> max-srcᵢ-var-dim Γ⊢psx 0<i
   max-srcᵢ-var-dim {Γ} {x} {A} {i} (pse {Γ = Δ} Γ⊢psx idp idp idp idp idp) 0<i | inr dA<i with dec-≤ (GSeTT.Syntax.dim A) (dim (snd (max-srcᵢ-var-def Γ⊢psx 0<i)))
   ... | inl dA≤m = let dA<dΔ = (S≤S (≤T (=-≤-= (ap S (GdimT {A} ^)) (S≤ dA≤m) (max-srcᵢ-var-dim Γ⊢psx 0<i ^)) (min≤m {i} {S (dimC (GPre-Ctx Δ))}))) in
                    ap (min i)
                    (ap S (simplify-max-l {max (dimC (GPre-Ctx Δ)) _} {dim (GPre-Ty A)} (≤T dA<dΔ (n≤max _ _))
                           >> simplify-max-l {dimC (GPre-Ctx Δ)} {_} (Sn≤m→n≤m dA<dΔ)))
                    >> max-srcᵢ-var-dim Γ⊢psx 0<i
   ... | inr m<dA = simplify-min-r {i} {S (max (max (dimC (GPre-Ctx Δ)) _) (dim (GPre-Ty A)))}
                      (up-maxS {max (dimC (GPre-Ctx Δ)) _} {dim (GPre-Ty A)}
                               (up-maxS {dimC (GPre-Ctx Δ)} {_}
                                  (min<l (=-≤ (ap S (max-srcᵢ-var-dim Γ⊢psx 0<i)) (≤T (S≤ (¬≤ m<dA)) (¬≤ dA<i))))
                                  (=-≤ (GdimT {A} ^) (≤T (n≤Sn _) (¬≤ dA<i))))
                               (=-≤ (ap S (GdimT {A}) ^) (¬≤ dA<i)))
                    >> ap S (simplify-max-r {max (dimC (GPre-Ctx Δ)) _} {dim (GPre-Ty A)}
                            (up-max {dimC (GPre-Ctx Δ)} {_} (≤-= (Sn≤m→n≤m (greater-than-min-r (¬≤ dA<i) (=-≤ (max-srcᵢ-var-dim Γ⊢psx 0<i) (¬≤ m<dA)))) (ap S GdimT)) (n≤Sn _)))

   max-srcᵢ-var : ∀ {Γ x A i} → (Γ⊢psx : Γ ⊢ps x # A) → 0 < i → Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-list (srcᵢ-var i Γ⊢psx)) × (min i (S (dimC (GPre-Ctx Γ))) == S (dim-tm Γ⊢x))})
   max-srcᵢ-var Γ⊢psx 0<i = (max-srcᵢ-var-def Γ⊢psx 0<i , max-srcᵢ-var-⊢ Γ⊢psx 0<i) , (max-srcᵢ-var-∈ Γ⊢psx 0<i , max-srcᵢ-var-dim Γ⊢psx 0<i)

   max-src-var : ∀ Γ → (Γ⊢ps : Γ ⊢ps) → (Γ ≠ (nil :: (0 , GSeTT.Syntax.∗))) → Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-set (src-var (Γ , Γ⊢ps))) × (dimC (GPre-Ctx Γ) == S (dim-tm Γ⊢x))})
   max-src-var Γ Γ⊢ps@(ps Γ⊢psx) Γ≠𝔻0 with max-srcᵢ-var {i = GSeTT.Syntax.dimC Γ} Γ⊢psx (dim-ps-not-𝔻0 Γ⊢ps Γ≠𝔻0)
   ... | ((x , B) , (x∈ , p)) = (x , B) , (∈-list-∈-set _ _ x∈ , (ap (λ n → min n (S (dimC (GPre-Ctx Γ)))) (GdimC {Γ}) >> simplify-min-l (n≤Sn _) ^ >> p) ) -- ((minS (GdimC {Γ}) ^) >> {!!} )) -- p))


   -- techincal : a full term contains a variable of dimension at least one minus the dimension of the context
   full-term-have-max-variables : ∀ {Γ A Γ⊢ps} → GPre-Ctx Γ ⊢T (Ty→Pre-Ty A) → A is-full-in ((Γ , Γ⊢ps)) →
     Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-set varT A) × (dimC (GPre-Ctx Γ) ≤ S (dim-tm Γ⊢x))})
   full-term-have-max-variables {Γ} {_} {Γ⊢ps} Γ⊢A (side-cond₁ .(_ , _) A t u (incl , incl₂) _) with max-src-var Γ Γ⊢ps (side-cond₁-not𝔻0 _ Γ⊢ps A t (Γ⊢src Γ⊢A) incl₂)
   ... | ((x , B) , Γ⊢x) , (x∈src , dimΓ=Sdimx) = ((x , B) , Γ⊢x) , (A∪B⊂A∪B∪C (varT A) (vart t) (vart u) _ (incl _ x∈src) , transport {B = λ x → (dimC (GPre-Ctx Γ)) ≤ x} dimΓ=Sdimx (n≤n _))
   full-term-have-max-variables {Γ} {_} {Γ⊢ps@(ps Γ⊢psx)} _ (side-cond₂ .(_ , _) _ (incl , _)) with max-var {Γ} Γ⊢ps
   ... | (x , B) , (x∈Γ , dimx) = ((x , (GPre-Ty B)) , var (GCtx Γ (psv Γ⊢psx)) (G#∈ x∈Γ)) , (incl _ (G∈ (x#A∈Γ→x∈Γ x∈Γ)) , ≤-= (=-≤ ((GdimC {Γ} ^) >> dimx) (n≤Sn _)) (ap S GdimT))

   well-foundedness : well-founded
   well-foundedness ((Γ , A) , Afull) Γ⊢A with full-term-have-max-variables Γ⊢A Afull
   ... |((x , B) , Γ⊢x) , (x∈Γ , dimΓ≤Sdimx) = ≤T dimΓ≤Sdimx (dim-∈-var Γ⊢x Γ⊢A x∈Γ)


   open import Globular-TT.Dec-Type-Checking J rule well-foundedness eqdecJ
