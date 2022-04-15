{-# OPTIONS --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Disks
open import GSeTT.Uniqueness-Derivations
open import GSeTT.Dec-Type-Checking
open import CaTT.Ps-contexts
open import CaTT.Relation
open import CaTT.Uniqueness-Derivations-Ps

module CaTT.Decidability-ps where
  ∅-is-not-ps : ∀ x A → ¬ (∅ ⊢ps x # A)
  ∅-is-not-ps x A ∅⊢psx with psvar ∅⊢psx
  ... | var _ ()

  ps-carrier : ∀{Γ A B C x y z} → ((Γ ∙ x # A) ∙ y # B) ⊢ps z # C → ((Σ Pre-Tm λ a → (a ⇒[ A ] Var x == B)) × (x == ℓ Γ)) × (y == S (ℓ Γ))
  ps-carrier (psd Γ⊢ps) = ps-carrier Γ⊢ps
  ps-carrier (pse _ idp idp idp idp idp) = ((_ , idp) , idp) , idp

  Γ+⊢ps→Γ⊢ps : ∀ {Γ x A a y B z} → ((Γ ∙ y # B) ∙ z # Var a ⇒[ B ] Var y) ⊢ps x # A → Γ ⊢ps a # B
  Γ+⊢ps→Γ⊢ps (psd Γ⊢ps) = Γ+⊢ps→Γ⊢ps Γ⊢ps
  Γ+⊢ps→Γ⊢ps (pse Γ⊢ps idp idp p idp idp) = transport ((=Var (snd (fst (=⇒ p)))) ^) Γ⊢ps

  𝔻0-var : ∀ x A → Pre-𝔻 0 ⊢t (Var x) # A → x == 0
  𝔻0-var x A (var _ (inr (idp , _))) = idp

  𝔻0-type : ∀ x A → Pre-𝔻 0 ⊢t (Var x) # A → A == ∗
  𝔻0-type x A (var _ (inr (idp , idp))) = idp

  ⊢psx→⊢ps : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢ps
  ⊢psx→⊢ps {A = ∗} Γ⊢psx = ps Γ⊢psx
  ⊢psx→⊢ps {A = Var _ ⇒[ A ] Var _} Γ⊢psx = ⊢psx→⊢ps (psd Γ⊢psx)

  dec-⊢-dim : ∀ {Γ} → Γ ⊢C → (n : ℕ) → dec (Σ (ℕ × Pre-Ty) (λ (x , A) → (Γ ⊢t (Var x) # A) × (dim A == n)))
  dec-⊢-dim {∅} _ n = inr λ{((x , A) , ((var _ ())  , _))}
  dec-⊢-dim {Γ ∙ x # A} Γ+⊢@(cc Γ⊢ _ _) n with eqdecℕ (dim A) n
  ... | inl idp = inl ((x , A) , (var Γ+⊢ (inr (idp , idp)) , idp))
  ... | inr dimA≠n with dec-⊢-dim Γ⊢ n
  ... | inl ((y , B) , ((var _ y∈Γ) , dimB=n)) = inl ((y , B ), (var Γ+⊢ (inl y∈Γ) , dimB=n))
  ... | inr ¬∃y = inr λ{((z , C) , ((var _ (inl z∈Γ)) , idp)) → ¬∃y ((z , C) , (var Γ⊢ z∈Γ , idp));
                        ((z , C) , ((var _ (inr (idp , idp))) , idp)) → dimA≠n idp}

  dim-pse : ∀ {Γ x A y B} → (Γ ∙ x # A) ∙ y # B ⊢ps y # B → (∀ z C → (Γ ∙ x # A) ∙ y # B ⊢ps z # C → dim C ≤ dim B)
  dim-pse Γ⊢psy z C (psd Γ⊢psf) = Sn≤m→n≤m (dim-pse Γ⊢psy _ _ Γ⊢psf)
  dim-pse Γ⊢psy z C (pse Γ⊢psz idp idp idp idp idp) = n≤n _

  private
    tgt-⟿ : ∀ {Γ x A y z a} → Γ ⊢t Var x # Var y ⇒[ A ] Var z → Γ , x ⟿ a → z ≠ a → Γ , z ⟿ a
    tgt-⟿ Γ⊢x (∂⁺⟿ Γ⊢'x) z≠a with unique-type Γ⊢x Γ⊢'x idp
    ... | idp = ⊥-elim (z≠a idp)
    tgt-⟿ Γ⊢x (x⟿∂⁺ Γ⊢'x x⟿a) z≠a with unique-type Γ⊢x Γ⊢'x idp
    ... | idp = x⟿a


  ⇒≠∗ : ∀ {A t u} → t ⇒[ A ] u ≠ ∗
  ⇒≠∗ ()

  dec-Σ⊢T : ∀ {Γ t} → dec (Σ Pre-Ty λ A → Γ ⊢t t # A)
  dec-Σ⊢T {∅} {Var x} = inr λ{(_ , var _ ())}
  dec-Σ⊢T {Γ+@(Γ ∙ y # B)} {Var x} with dec-⊢C Γ+ | eqdecℕ x y
  ... | inr Γ+⊬ | _ = inr λ (A , Γ+⊢x) → Γ+⊬ (Γ⊢t:A→Γ⊢ Γ+⊢x)
  ... | inl Γ+⊢ | inl idp = inl (B , var Γ+⊢ (inr (idp , idp)))
  ... | inl Γ+⊢ | inr x≠y with dec-Σ⊢T {Γ} {Var x}
  ... | inl (A , Γ⊢x)= inl (A , wkt Γ⊢x Γ+⊢)
  ... | inr Γ⊬x = inr λ{ (B , var _ (inr (idp , idp))) → x≠y idp;
                         (B , var (cc Γ⊢ _ _) (inl x#B∈Γ)) → Γ⊬x (B , var Γ⊢ x#B∈Γ)}

  dec-⟿ : ∀ Γ x y → dec (Γ , x ⟿ y)
  dec-⟿-aux : ∀ Γ x A y → Γ ⊢t (Var x) # A → dec (Γ , x ⟿ y)
  dec-⟿-aux Γ x ∗ y Γ⊢x = inr λ{(∂⁺⟿ Γ⊢'x) → ⇒≠∗ (unique-type Γ⊢'x Γ⊢x idp) ; (x⟿∂⁺ Γ⊢'x _) → ⇒≠∗ (unique-type Γ⊢'x Γ⊢x idp)}
  dec-⟿-aux Γ x (Var _ ⇒[ A ] Var z) y Γ⊢x with eqdecℕ z y | dec-⟿-aux Γ z A y (Γ⊢tgt (Γ⊢t:A→Γ⊢A Γ⊢x))
  ... | inl idp | _ = inl (∂⁺⟿ Γ⊢x)
  ... | inr _ | inl x⟿z = inl (x⟿∂⁺ Γ⊢x x⟿z)
  ... | inr z≠y | inr ¬x⟿z = inr λ x⟿y → ¬x⟿z (tgt-⟿ Γ⊢x x⟿y z≠y)
  dec-⟿ Γ x y with dec-Σ⊢T {Γ} {Var x}
  ... | inr Γ⊬x = inr λ{(∂⁺⟿ Γ⊢x) → Γ⊬x (_ , Γ⊢x) ; (x⟿∂⁺ Γ⊢x _) → Γ⊬x (_ , Γ⊢x)}
  ... | inl (A , Γ⊢x) = dec-⟿-aux Γ x A y Γ⊢x

  Γ⊢psx-dim-⟿ : ∀ {Γ x A y B} → Γ ⊢ps x # A → Γ ⊢ps y # B → dim B < dim A → Γ , x ⟿ y
  Γ⊢psx-dim-⟿ Γ⊢psx pss dB<dA with 𝔻0-type _ _ (psvar Γ⊢psx)
  ... | idp = ⊥-elim (Sn≰n _ dB<dA)
  Γ⊢psx-dim-⟿ {Γ} {x} {A} {y} {B} Γ⊢psx (psd Γ⊢psf) dB<dA with eqdecℕ (S (dim B)) (dim A)
  ... | inl SdB=dA = transport {B = λ a → Γ , a ⟿ y} (Γ⊢psx-dim Γ⊢psf Γ⊢psx SdB=dA) (∂⁺⟿ (psvar Γ⊢psf))
  ... | inr SdB≠dA = T⟿ (Γ⊢psx-dim-⟿ Γ⊢psx Γ⊢psf (≤×≠→< dB<dA SdB≠dA)) (∂⁺⟿ (psvar Γ⊢psf))
  Γ⊢psx-dim-⟿ Γ⊢psx Γ⊢psy@(pse _ idp idp idp idp idp) dB<dA = ⊥-elim (Sn≰n _ (≤T dB<dA (dim-pse Γ⊢psy _ _ Γ⊢psx)))

  ⟿→psx : ∀ {Γ x A y} → Γ ⊢ps x # A → Γ , x ⟿ y → Σ Pre-Ty λ B → Γ ⊢ps y # B
  ⟿→psx Γ⊢psx (∂⁺⟿ Γ⊢x) with unique-type (psvar Γ⊢psx) Γ⊢x idp
  ... | idp = _ , (psd Γ⊢psx)
  ⟿→psx Γ⊢psx (x⟿∂⁺ Γ⊢x z⟿y) with unique-type (psvar Γ⊢psx) Γ⊢x idp
  ... | idp = ⟿→psx (psd Γ⊢psx) z⟿y

  pse-max : ∀ {Γ x A y B} → (Γ ∙ x # A) ∙ y # B ⊢ps y # B → (∀ z C → (Γ ∙ x # A) ∙ y # B ⊢ps z # C → (y == z) + ((Γ ∙ x # A) ∙ y # B , y ⟿ z))
  pse-max {B = B} Γ⊢psy z C Γ⊢psz with ℕ-trichotomy (dim B) (dim C)
  ... | inl (inl dimB<dimC) = ⊥-elim (Sn≰n _ (≤T dimB<dimC (dim-pse Γ⊢psy _ _ Γ⊢psz)) )
  ... | inl (inr dimC<dimB) = inr (Γ⊢psx-dim-⟿ Γ⊢psy Γ⊢psz dimC<dimB)
  ... | inr dimB=dimC = inl (Γ⊢psx-dim Γ⊢psy Γ⊢psz dimB=dimC)

  ⊢psx→max : ∀ {Γ x A} → Γ ⊢ps x # A → (Σ (ℕ × Pre-Ty) λ (y , B) → (Γ ⊢ps y # B) × (∀ z C → Γ ⊢ps z # C → (y == z) + (Γ , y ⟿ z)))
  ⊢psx→max pss = (0 , ∗) , (pss , λ z C 𝔻0⊢psx → inl (𝔻0-var z C (psvar 𝔻0⊢psx) ^))
  ⊢psx→max (psd Γ⊢psx) = ⊢psx→max Γ⊢psx
  ⊢psx→max {((Γ ∙ _ # B) ∙ _ # C)} {x} {A} Γ+⊢ps@(pse Γ⊢psx idp idp idp idp idp) = (S (ℓ Γ) , C) , (Γ+⊢ps , pse-max Γ+⊢ps)


  -- TODO : move case_of_ in Prelude
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

  ill-formed-1st-var : ∀ {y A} → ¬ (∅ ∙ S y # A ⊢C)
  ill-formed-1st-var (cc _ _ ())

  ill-formed-1st-type : ∀ {y A a b} → ¬ ((∅ ∙ y # a ⇒[ A ] b) ⊢C)
  ill-formed-1st-type (cc _ (ar _ (var _ ()) _) _)

  dec-⊢psx-max : ∀ {Γ} → dec (Σ (ℕ × Pre-Ty) λ (x , A) → (Γ ⊢ps x # A) × (∀ y B → Γ ⊢ps y # B → (x == y) + (Γ , x ⟿ y)))
  dec-⊢psx-max {∅} = inr λ ((x , A) , (nil⊢psx , _ )) → ∅-is-not-ps _ _ nil⊢psx
  dec-⊢psx-max {∅ ∙ O # ∗} = inl ((0 , ∗) , (pss , λ y B  𝔻0⊢psy → inl (𝔻0-var _ _ (psvar 𝔻0⊢psy) ^)))
  dec-⊢psx-max {∅ ∙ O # _ ⇒[ _ ] _} = inr λ ((x , A) , (Γ⊢psx , _ )) → ill-formed-1st-type (psv Γ⊢psx)
  dec-⊢psx-max {∅ ∙ S z # C} = inr λ ((x , A) , (Γ⊢psx , _ )) → ill-formed-1st-var (psv Γ⊢psx)
  dec-⊢psx-max {(Γ ∙ z # C) ∙ f # ∗} = inr λ ((x , A) , (Γ+⊢psx , _)) → ⇒≠∗ (snd (fst (fst (ps-carrier Γ+⊢psx))))
  dec-⊢psx-max {(Γ ∙ z # C) ∙ f # Var a ⇒[ D ] Var b} with eqdec-PreTy C D | eqdecℕ z (ℓ Γ) | eqdecℕ (ℓ Γ) b | eqdecℕ f (S (ℓ Γ))
  ... | inr C≠D | _ | _ | _  = inr λ ((x , A) , (Γ+⊢psx , _)) → C≠D (fst (fst (=⇒ (snd (fst (fst (ps-carrier Γ+⊢psx)))))))
  ... | inl idp | inr z≠l | _ | _  = inr λ ((x , A) , (Γ+⊢psx , _)) → z≠l (snd (fst (ps-carrier Γ+⊢psx)))
  ... | inl idp | inl idp | inr l≠b | _  = inr λ ((x , A) , (Γ+⊢psx , _)) → l≠b (=Var (snd (=⇒ (snd (fst (fst (ps-carrier Γ+⊢psx)))))))
  ... | inl idp | inl idp | inl idp | inr f≠Sl  = inr λ ((x , A) , (Γ+⊢psx , _)) → f≠Sl (snd (ps-carrier Γ+⊢psx))
  ... | inl idp | inl idp | inl idp | inl idp with dec-⊢psx-max {Γ}
  ... | inr ¬Γ⊢ps = inr λ ((x , A) , (Γ+⊢psx , _)) → ¬Γ⊢ps (⊢psx→max (Γ+⊢ps→Γ⊢ps Γ+⊢psx))
  ... | inl ((c , E) , (Γ⊢psc , cmax)) with eqdecℕ c a | eqdec-PreTy E C
  ... | inl idp | inl idp = let Γ+⊢ps = pse Γ⊢psc idp idp idp idp idp in inl ((S (ℓ Γ) , Var a ⇒[ C ] Var (ℓ Γ)) , (Γ+⊢ps , pse-max Γ+⊢ps))
  ... | inl idp | inr E≠C = inr λ ((x , A) , (Γ+⊢psx , _)) → E≠C (unique-type (psvar Γ⊢psc) (psvar (Γ+⊢ps→Γ⊢ps Γ+⊢psx)) idp)
  ... | inr c≠a | _ with dec-⟿ Γ c a
  ... | inr ¬c⟿a = inr λ ((x , A) , (Γ+⊢psx , _)) → case cmax _ _ (Γ+⊢ps→Γ⊢ps Γ+⊢psx) of λ{(inl c=a) → c≠a c=a; (inr c⟿a) → ¬c⟿a c⟿a }
  ... | inl c⟿a with (⟿→psx Γ⊢psc c⟿a)
  ... | (F , Γ⊢psa) with eqdec-PreTy F C
  ... | inl idp = let Γ+⊢ps = pse Γ⊢psa idp idp idp idp idp in inl ((S (ℓ Γ) , Var a ⇒[ C ] Var (ℓ Γ)) , (Γ+⊢ps  , pse-max Γ+⊢ps))
  ... | inr F≠C = inr λ ((x , A) , (Γ+⊢psx , _)) → F≠C (unique-type (psvar Γ⊢psa) (psvar (Γ+⊢ps→Γ⊢ps Γ+⊢psx)) idp)

  dec-⊢ps : ∀ Γ → dec(Γ ⊢ps)
  dec-⊢ps Γ with dec-⊢psx-max {Γ}
  ... | inl ((x , A) , (Γ⊢psx , _)) = inl (⊢psx→⊢ps Γ⊢psx)
  ... | inr ¬Γ⊢psx = inr λ {(ps Γ⊢psy) → ¬Γ⊢psx (⊢psx→max Γ⊢psy)}
