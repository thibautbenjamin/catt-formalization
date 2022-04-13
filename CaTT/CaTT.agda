{-# OPTIONS --without-K #-}

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
   Ty→Pre-Ty (t ⇒[ A ] u) = (Tm→Pre-Tm t) ⇒[ Ty→Pre-Ty A ] (Tm→Pre-Tm u)

   Tm→Pre-Tm (v x) = Var x
   Tm→Pre-Tm (coh Γ A Afull γ) = Tm-constructor (((Γ , A)) , Afull) (Sub→Pre-Sub γ)

   Sub→Pre-Sub <> = <>
   Sub→Pre-Sub < γ , x ↦ t > = < Sub→Pre-Sub γ , x ↦ Tm→Pre-Tm t >

   _[_]Ty : Ty → Sub → Ty
   _[_]Tm : Tm → Sub → Tm
   _∘ₛ_ : Sub → Sub → Sub

   ∗ [ σ ]Ty = ∗
   (t ⇒[ A ] u) [ σ ]Ty = (t [ σ ]Tm) ⇒[ A [ σ ]Ty ] (u [ σ ]Tm)
   v x [ <> ]Tm = v x
   v x [ < σ , y ↦ t > ]Tm = if x ≡ y then t else ((v x) [ σ ]Tm)
   coh Γ A full γ [ σ ]Tm = coh Γ A full (γ ∘ₛ σ)
   <> ∘ₛ γ = <>
   < γ , x ↦ t > ∘ₛ δ = < γ ∘ₛ δ , x ↦ t [ δ ]Tm >

   GPre-Ty→Ty : GSeTT.Syntax.Pre-Ty → Ty
   GPre-Ty→Ty GSeTT.Syntax.∗ = ∗
   GPre-Ty→Ty ((GSeTT.Syntax.Var x) GSeTT.Syntax.⇒[ A ] (GSeTT.Syntax.Var y)) = v x ⇒[ GPre-Ty→Ty A ] v y

   Ty→Pre-Ty[] : ∀ {A γ} → ((GPre-Ty A) [ Sub→Pre-Sub γ ]Pre-Ty) == Ty→Pre-Ty ((GPre-Ty→Ty A) [ γ ]Ty)
   Tm→Pre-Tm[] : ∀ {x γ} → ((Var x) [ Sub→Pre-Sub γ ]Pre-Tm) == Tm→Pre-Tm ((v x) [ γ ]Tm)
   Ty→Pre-Ty[] {GSeTT.Syntax.∗} {γ} = idp
   Ty→Pre-Ty[] {(GSeTT.Syntax.Var x) GSeTT.Syntax.⇒[ A ] (GSeTT.Syntax.Var y)} {γ} = ap³ _⇒[_]_  (Tm→Pre-Tm[] {x} {γ}) Ty→Pre-Ty[] (Tm→Pre-Tm[] {y} {γ})
   Tm→Pre-Tm[] {x} {<>} = idp
   Tm→Pre-Tm[] {x} {< γ , y ↦ t >} with eqdecℕ x y
   ... | inl idp = idp
   ... | inr _ = Tm→Pre-Tm[] {x} {γ}

   dim-Pre-Ty[] : ∀ {A γ} → dim (Ty→Pre-Ty ((GPre-Ty→Ty A) [ γ ]Ty)) == dim (GPre-Ty A)
   dim-Pre-Ty[] {GSeTT.Syntax.∗} {γ} = idp
   dim-Pre-Ty[] {(GSeTT.Syntax.Var _) GSeTT.Syntax.⇒[ A ](GSeTT.Syntax.Var _)} {γ} = ap S dim-Pre-Ty[]

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
   ...                                           | inl idp | inr A≠A' = inr λ{A=A' → A≠A' (snd (=, (fst-is-inj A=A')))}

   open import Globular-TT.Uniqueness-Derivations J rule eqdecJ
   open import Globular-TT.Disks J rule eqdecJ

   dim-tm : ∀ {Γ x A} → Γ ⊢t Var x # A → ℕ
   dim-tm {Γ} {x} {A} _ = dim A

   GdimT : ∀ {A} → GSeTT.Syntax.dim A == dim (GPre-Ty A)
   GdimT {GSeTT.Syntax.∗} = idp
   GdimT {_ GSeTT.Syntax.⇒[ A ] _} = ap S GdimT

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
   ... | inl dA≤m = let dA<dΔ = (S≤S (≤T (=-≤-= (ap S (GdimT {A} ^)) (S≤ dA≤m) (max-srcᵢ-var-dim Γ⊢psx 0<i ^)) (min≤m i (S (dimC (GPre-Ctx Δ)))))) in
                    ap (min i)
                    (ap S (simplify-max-l {max (dimC (GPre-Ctx Δ)) _} {dim (GPre-Ty A)} (≤T dA<dΔ (n≤max _ _))
                           >> simplify-max-l {dimC (GPre-Ctx Δ)} {_} (Sn≤m→n≤m dA<dΔ)))
                    >> max-srcᵢ-var-dim Γ⊢psx 0<i
   ... | inr m<dA = simplify-min-r {i} {S (max (max (dimC (GPre-Ctx Δ)) _) (dim (GPre-Ty A)))}
                      (up-maxS {max (dimC (GPre-Ctx Δ)) _} {dim (GPre-Ty A)}
                               (up-maxS {dimC (GPre-Ctx Δ)} {_}
                                  (min<l (=-≤ (ap S (max-srcᵢ-var-dim Γ⊢psx 0<i)) (≤T (S≤ (≰ m<dA)) (≰ dA<i))))
                                  (=-≤ (GdimT {A} ^) (≤T (n≤Sn _) (≰ dA<i))))
                               (=-≤ (ap S (GdimT {A}) ^) (≰ dA<i)))
                    >> ap S (simplify-max-r {max (dimC (GPre-Ctx Δ)) _} {dim (GPre-Ty A)}
                            (up-max {dimC (GPre-Ctx Δ)} {_} (≤-= (Sn≤m→n≤m (greater-than-min-r (≰ dA<i) (=-≤ (max-srcᵢ-var-dim Γ⊢psx 0<i) (≰ m<dA)))) (ap S GdimT)) (n≤Sn _)))

   max-srcᵢ-var : ∀ {Γ x A i} → (Γ⊢psx : Γ ⊢ps x # A) → 0 < i → Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-list (srcᵢ-var i Γ⊢psx)) × (min i (S (dimC (GPre-Ctx Γ))) == S (dim-tm Γ⊢x))})
   max-srcᵢ-var Γ⊢psx 0<i = (max-srcᵢ-var-def Γ⊢psx 0<i , max-srcᵢ-var-⊢ Γ⊢psx 0<i) , (max-srcᵢ-var-∈ Γ⊢psx 0<i , max-srcᵢ-var-dim Γ⊢psx 0<i)

   max-src-var : ∀ Γ → (Γ⊢ps : Γ ⊢ps) → (Γ ≠ (nil :: (0 , GSeTT.Syntax.∗))) → Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-set (src-var (Γ , Γ⊢ps))) × (dimC (GPre-Ctx Γ) == S (dim-tm Γ⊢x))})
   max-src-var Γ Γ⊢ps@(ps Γ⊢psx) Γ≠𝔻0 with max-srcᵢ-var {i = GSeTT.Syntax.dimC Γ} Γ⊢psx (dim-ps-not-𝔻0 Γ⊢ps Γ≠𝔻0)
   ... | ((x , B) , (x∈ , p)) = (x , B) , (∈-list-∈-set _ _ x∈ , (ap (λ n → min n (S (dimC (GPre-Ctx Γ)))) (GdimC {Γ}) >> simplify-min-l (n≤Sn _) ^ >> p) )

   full-term-have-max-variables : ∀ {Γ A Γ⊢ps} → GPre-Ctx Γ ⊢T (Ty→Pre-Ty A) → A is-full-in ((Γ , Γ⊢ps)) →
     Σ (Σ (ℕ × Pre-Ty) (λ {(x , B) → GPre-Ctx Γ ⊢t Var x # B})) (λ {((x , B) , Γ⊢x) → (x ∈-set varT A) × (dimC (GPre-Ctx Γ) ≤ S (dim-tm Γ⊢x))})
   full-term-have-max-variables {Γ} {_} {Γ⊢ps} Γ⊢A (side-cond₁ .(_ , _) A t u (incl , incl₂) _) with max-src-var Γ Γ⊢ps (side-cond₁-not𝔻0 _ Γ⊢ps A t (Γ⊢src Γ⊢A) incl₂)
   ... | ((x , B) , Γ⊢x) , (x∈src , dimΓ=Sdimx) = ((x , B) , Γ⊢x) , (A∪B⊂A∪B∪C (varT A) (vart t) (vart u) _ (incl _ x∈src) , transport {B = λ x → (dimC (GPre-Ctx Γ)) ≤ x} dimΓ=Sdimx (n≤n _))
   full-term-have-max-variables {Γ} {_} {Γ⊢ps@(ps Γ⊢psx)} _ (side-cond₂ .(_ , _) _ (incl , _)) with max-var {Γ} Γ⊢ps
   ... | (x , B) , (x∈Γ , dimx) = ((x , (GPre-Ty B)) , var (GCtx Γ (psv Γ⊢psx)) (G#∈ x∈Γ)) , (incl _ (G∈ (x#A∈Γ→x∈Γ x∈Γ)) , ≤-= (=-≤ ((GdimC {Γ} ^) >> dimx) (n≤Sn _)) (ap S GdimT))

   dim-∈-var : ∀ {Γ A x B} → Γ ⊢t Var x # B → Γ ⊢T (Ty→Pre-Ty A) → x ∈-set varT A → dim B < dim (Ty→Pre-Ty A)
   dim-∈-var-t : ∀ {Γ t A x B} → Γ ⊢t Var x # B → Γ ⊢t (Tm→Pre-Tm t) # (Ty→Pre-Ty A) → x ∈-set vart t → dim B ≤ dim (Ty→Pre-Ty A)
   dim-∈-var-S : ∀ {Δ γ Γ x B} → Δ ⊢t Var x # B → Δ ⊢S (Sub→Pre-Sub γ) > (GPre-Ctx Γ) → x ∈-set varS γ → dim B ≤ dimC (GPre-Ctx Γ)
   dim-full-ty : ∀ {Γ A} → (Γ⊢ps : Γ ⊢ps) → (GPre-Ctx Γ) ⊢T (Ty→Pre-Ty A) → A is-full-in (Γ , Γ⊢ps) → dimC (GPre-Ctx Γ) ≤ dim (Ty→Pre-Ty A)

   dim-∈-var {Γ} {A⇒@(t ⇒[ A ] u)} {x} {B} Γ⊢x (ar Γ⊢A Γ⊢t Γ⊢u) x∈A⇒ with ∈-∪ {varT A} {vart t ∪-set vart u} x∈A⇒
   ... | inl x∈A = n≤m→n≤Sm (dim-∈-var Γ⊢x Γ⊢A x∈A)
   ... | inr x∈t∪u with ∈-∪ {vart t} {vart u} x∈t∪u
   ... | inl x∈t = S≤ (dim-∈-var-t Γ⊢x Γ⊢t x∈t)
   ... | inr x∈u = S≤ (dim-∈-var-t Γ⊢x Γ⊢u x∈u)
   dim-∈-var-t {t = v x} Γ⊢x Γ⊢t (inr idp) with unique-type Γ⊢x Γ⊢t (ap Var idp)
   ... | idp = n≤n _
   dim-∈-var-t {t = coh Γ A Afull γ} Γ⊢x (tm Γ⊢A Δ⊢γ:Γ p) x∈t = ≤-= (≤T (dim-∈-var-S Γ⊢x Δ⊢γ:Γ x∈t) (dim-full-ty (snd Γ) Γ⊢A Afull) ) ((dim[] _ _ ^) >> ap dim (p ^))
   dim-∈-var-S {Δ} {< γ , y ↦ t >} {Γ :: (_ , A)} {x} {B} Δ⊢x (sc Δ⊢γ:Γ Γ+⊢ Δ⊢t idp) x∈γ+ with ∈-∪ {varS γ} {vart t} x∈γ+
   ... | inl x∈γ = ≤T (dim-∈-var-S Δ⊢x Δ⊢γ:Γ x∈γ) (n≤max _ _)
   ... | inr x∈t = ≤T (dim-∈-var-t Δ⊢x (transport {B = Δ ⊢t (Tm→Pre-Tm t) #_} Ty→Pre-Ty[] Δ⊢t) x∈t) (=-≤ (dim-Pre-Ty[]) (m≤max (dimC (GPre-Ctx Γ)) (dim (GPre-Ty A))))
   dim-full-ty Γ⊢ps Γ⊢A Afull with full-term-have-max-variables Γ⊢A Afull
   ... | ((x , B) , Γ⊢x) , (x∈A , dimx) = ≤T dimx (dim-∈-var Γ⊢x Γ⊢A x∈A)

   well-foundedness : well-founded
   well-foundedness ((Γ , A) , Afull) Γ⊢A with full-term-have-max-variables Γ⊢A Afull
   ... |((x , B) , Γ⊢x) , (x∈Γ , dimΓ≤Sdimx) = ≤T dimΓ≤Sdimx (dim-∈-var Γ⊢x Γ⊢A x∈Γ)

   open import Globular-TT.Dec-Type-Checking J rule well-foundedness eqdecJ
