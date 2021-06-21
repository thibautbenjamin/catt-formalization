{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

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
  {- To prove termination -}
  _,_⋖₀_ : ∀ Γ x y → Set₁
  Γ , x ⋖₀ y = (Γ , x ◃ y) × (∀ z → ¬ ((Γ , x ◃ z) × (Γ , z ◃ y)))

  data _,_⋖_ : ∀ Γ x y → Set₁ where
    ε : ∀ {Γ x} → Γ , x ⋖ x
    ⋖T : ∀ {Γ x y z} → Γ , x ⋖ y → Γ , y ⋖₀ z → Γ , x ⋖ z

  ℓ : ∀ {Γ x y} → Γ , x ⋖ y → ℕ
  ℓ ε = 0
  ℓ (⋖T x⋖y y⋖₀z) = S (ℓ x⋖y)

  ∅-is-not-ps : ∀ x A → ¬ (nil ⊢ps x # A)
  ∅-is-not-ps x A ∅⊢psx with psvar ∅⊢psx
  ... | var _ ()

  -- ∅-⊢T : ∀ A → nil ⊢T A → A == ∗
  -- ∅-⊢T = {!!}

  -- ¬ps-ends-by-object : ∀ {Γ x y A} → Γ ≠ nil → ¬ ((Γ :: (x , ∗)) ⊢ps y # A)
  -- ¬ps-ends-by-object Γ≠nil pss = Γ≠nil idp
  -- ¬ps-ends-by-object Γ≠nil (psd Γ⊢ps) = ¬ps-ends-by-object Γ≠nil Γ⊢ps

  ps-carrier : ∀{Γ A B C x y z} → ((Γ :: (x , A)) :: (y , B)) ⊢ps z # C → ((Σ Pre-Tm λ a → (⇒ A a (Var x) == B)) × (x == length Γ)) × (y == S (length Γ))
  ps-carrier (psd Γ⊢ps) = ps-carrier Γ⊢ps
  ps-carrier (pse _ idp idp idp idp idp) = ((_ , idp) , idp) , idp

  -- ¬ps-carrier : ∀ {Γ x y z A B C} → (∀ a → B ≠ ⇒ A a (Var x)) → ¬ (((Γ :: (x , A)) :: (y , B)) ⊢ps z # C)
  -- ¬ps-carrier = {!!}

  Γ+⊢ps→Γ⊢ps : ∀ {Γ x A a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) ⊢ps x # A → Γ ⊢ps a # B
  Γ+⊢ps→Γ⊢ps (psd Γ⊢ps) = Γ+⊢ps→Γ⊢ps Γ⊢ps
  Γ+⊢ps→Γ⊢ps (pse Γ⊢ps idp idp p idp idp) = transport ((=Var (snd (fst (=⇒ p)))) ^) Γ⊢ps

  Γ⊢psx-dim-ty : ∀ {Γ x y A B} → Γ ⊢ps x # A → Γ ⊢ps y # B → dim A == dim B → A == B
  Γ⊢psx-dim-ty Γ⊢psx Γ⊢psy p = unique-type (psvar Γ⊢psx) (psvar Γ⊢psy) (Var= (Γ⊢psx-dim Γ⊢psx Γ⊢psy p))

  last-var-lm : ∀ {Γ x A a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) ⊢ps x # A → dim A ≤ S (dim B)
  last-var-lm (psd Γ⊢psf) = Sn≤m→n≤m (last-var-lm Γ⊢psf)
  last-var-lm (pse _ idp idp _ idp idp) = n≤n _

  last-var-ps : ∀ {Γ x A a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) ⊢ps x # A → dim A == S (dim B) → x == z
  last-var-ps (psd Γ⊢psf) p = ⊥-elim (Sn≰n-t p (last-var-lm Γ⊢psf))
  last-var-ps (pse Γ⊢psx idp idp _ idp idp) _ = idp

  𝔻0-var : ∀ x A → Pre-𝔻 0 ⊢t (Var x) # A → x == 0
  𝔻0-var x A (var _ (inr (idp , _))) = idp

  𝔻0-type : ∀ x A → Pre-𝔻 0 ⊢t (Var x) # A → A == ∗
  𝔻0-type x A (var _ (inr (idp , idp))) = idp

  ⊢psx→⊢ps : ∀ {Γ x A} → Γ ⊢ps x # A → Γ ⊢ps
  ⊢psx→⊢ps {A = ∗} Γ⊢psx = ps Γ⊢psx
  ⊢psx→⊢ps {A = ⇒ A (Var _) (Var _)} Γ⊢psx = ⊢psx→⊢ps (psd Γ⊢psx)

  dec-⊢-dim : ∀ {Γ} → Γ ⊢C → (n : ℕ) → dec (Σ (ℕ × Pre-Ty) (λ (x , A) → (Γ ⊢t (Var x) # A) × (dim A == n)))
  dec-⊢-dim {nil} _ n = inr λ{((x , A) , ((var _ ())  , _))}
  dec-⊢-dim {Γ :: (x , A)} Γ+⊢@(cc Γ⊢ _ _) n with eqdecℕ (dim A) n
  ... | inl idp = inl ((x , A) , (var Γ+⊢ (inr (idp , idp)) , idp))
  ... | inr dimA≠n with dec-⊢-dim Γ⊢ n
  ... | inl ((y , B) , ((var _ y∈Γ) , dimB=n)) = inl ((y , B ), (var Γ+⊢ (inl y∈Γ) , dimB=n))
  ... | inr ¬∃y = inr λ{((z , C) , ((var _ (inl z∈Γ)) , idp)) → ¬∃y ((z , C) , (var Γ⊢ z∈Γ , idp));
                        ((z , C) , ((var _ (inr (idp , idp))) , idp)) → dimA≠n idp}


  dec-◃ : ∀ Γ x y → dec (Γ , x ◃ y)
  dec-◃ Γ x y = {!!}

  dec-⋖ : ∀ Γ x y → dec (Γ , x ⋖ y)
  dec-⋖ = {!!}

  ⋖∈ : ∀ {Γ x y} → Γ , x ⋖₀ y → y ∈ Γ
  ⋖∈ (x◃y , _) = ◃∈ x◃y


  ∈⋖ : ∀ {Γ x y} → Γ , x ⋖₀ y → x ∈ Γ
  ∈⋖ (x◃y , _) = ∈◃ x◃y

  ⋖-next-ps : ∀ {Γ x A a b c} → Γ ⊢ps x # A → Γ , a ⋖₀ b → Γ , a ⋖₀ c → b == c
  ⋖-next-ps Γ⊢psx a⋖₀b@(a◃b , minb) a⋖₀c@(a◃c , minc) with psx-◃-linear→ Γ⊢psx _ _ (⋖∈ a⋖₀b) (⋖∈ a⋖₀c)
  ... | inl (inl b◃c) = ⊥-elim (minc _ (a◃b , b◃c))
  ... | inl (inr c◃b) = ⊥-elim (minb _ (a◃c , c◃b))
  ... | inr idp = idp

  ⋖-prev-ps : ∀ {Γ x A a b c} → Γ ⊢ps x # A → Γ , a ⋖₀ c → Γ , b ⋖₀ c → a == b
  ⋖-prev-ps Γ⊢psx a⋖₀c@(a◃c , mina) b⋖₀c@(b◃c , minb) with psx-◃-linear→ Γ⊢psx _ _ (∈⋖ a⋖₀c) (∈⋖ b⋖₀c)
  ... | inl (inl a◃b) = ⊥-elim (mina _ (a◃b , b◃c))
  ... | inl (inr b◃a) = ⊥-elim (minb _ (b◃a , a◃c))
  ... | inr idp = idp

  ⊢◃ : ∀ {Γ x y} → Γ , x ◃ y → Σ Pre-Ty λ A → Γ ⊢t Var y # A
  ⊢◃ = {!!}


  ◃⊢ : ∀ {Γ x y} → Γ , x ◃ y → Σ Pre-Ty λ A → Γ ⊢t Var x # A
  ◃⊢ = {!!}


  ⊢ps⋖-min : ∀ {Γ x A b c} → Γ ⊢ps x # ⇒ A (Var b) (Var c) → (∀ z → ¬ ((Γ , x ◃ z) × (Γ , z ◃ c)))
  ⊢ps⋖-min Γ⊢psx z (x◃z , z◃c) with ⊢◃ x◃z | ◃⊢ z◃c
  ... | B , Γ⊢z | C , Γ⊢'z with unique-type Γ⊢z Γ⊢'z idp
  ... | idp =
    let x⟿z = ⊢psx-◃→⟿ Γ⊢psx x◃z in
    n≮n _ (≤T (⟿dim (psvar Γ⊢psx) Γ⊢z x⟿z) (⟿dim Γ⊢'z (Γ⊢tgt (Γ⊢t:A→Γ⊢A (psvar Γ⊢psx))) (⊢psx-◃→⟿+ Γ⊢psx x⟿z z◃c)))

  ⊢ps⋖ : ∀ {Γ x A b c} → Γ ⊢ps x # ⇒ A (Var b) (Var c) → Γ , x ⋖₀ c
  ⊢ps⋖ Γ⊢psx = gen (◃∂⁺ (psvar Γ⊢psx)) , ⊢ps⋖-min Γ⊢psx


  ⊢ps⋖-∂⁻ : ∀ {Γ x A b c} → Γ ⊢ps x # ⇒ A (Var b) (Var c) → Γ , b ⋖₀ x
  ⊢ps⋖-∂⁻ = {!!}

  l-is-0 : ∀ {Γ : Pre-Ctx} → length Γ == 0 → Γ == nil
  l-is-0 {nil} p = idp


  0-not-tgt : ∀ {Γ x A a b c B} → Γ ⊢ps x # A  → Γ ⊢t a # ⇒ B (Var b) (Var c) → c ≠ 0
  0-not-tgt pss (var _ (inl ())) c=0
  0-not-tgt pss (var _ (inr ())) c=0
  0-not-tgt (psd Γ⊢ps) Γ⊢a c=0 = 0-not-tgt Γ⊢ps Γ⊢a c=0
  0-not-tgt (pse Γ⊢ps idp idp idp idp idp) (var _ (inl (inl a∈Γ))) z=0 = 0-not-tgt Γ⊢ps (var (psv Γ⊢ps) a∈Γ) z=0
  0-not-tgt (pse Γ⊢ps idp idp idp idp idp) (var _ (inl (inr (idp , idp)))) z=0 = 0-not-tgt Γ⊢ps (psvar Γ⊢ps) z=0
  0-not-tgt (pse {_} {b} {B} Γ⊢ps idp idp idp idp idp) (var _ (inr (idp , idp))) z=0 = ∅-is-not-ps b B (transport {B = λ Γ → Γ ⊢ps b # B} (l-is-0 z=0) Γ⊢ps)

  ps-not-0 : ∀ {Γ x A} → Γ ≠ Pre-𝔻 0 → Γ ⊢ps x # A → x ≠ 0
  ps-not-0 Γ≠𝔻0 pss x=0 = Γ≠𝔻0 idp
  ps-not-0 Γ≠𝔻0 (psd Γ⊢ps) x=0 = 0-not-tgt Γ⊢ps (psvar Γ⊢ps) x=0
  ps-not-0 Γ≠𝔻0 (pse Γ⊢ps idp idp idp idp idp) ()

  strengthen-⋖ : ∀ {Γ a y B z} → ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) , 0 ⋖ a → Γ , 0 ⋖ a
  strengthen-⋖ = {!!}

  ℓ-strengthen : ∀ {Γ a y B z} → (0⋖a : ((Γ :: (y , B)) :: (z , ⇒ B (Var a) (Var y))) , 0 ⋖ a) → ℓ 0⋖a == ℓ (strengthen-⋖ 0⋖a)
  ℓ-strengthen = {!!}

  Sn≠0 : ∀ n → S n ≠ 0
  Sn≠0 n ()

  ill-formed-1st-var : ∀ {y A} → ¬ ((nil :: (S y , A)) ⊢C)
  ill-formed-1st-var (cc _ _ ())

  ill-formed-1st-type : ∀ {y A a b} → ¬ ((nil :: (y , ⇒ A a b)) ⊢C)
  ill-formed-1st-type (cc _ (ar (var _ ()) _) _)

  ⇒≠∗ : ∀ {A t u} → ⇒ A t u ≠ ∗
  ⇒≠∗ ()

  dec-⊢psx-dim : ∀ {Γ} →  (n : ℕ) → (m : ℕ) → (0⋖m : Γ , 0 ⋖ m) → (l : ℕ) → l == ℓ 0⋖m → dec (Σ (ℕ × Pre-Ty) (λ (x , A) → (Γ ⊢ps x # A) × ((dim A == n) × (x == m))))

  dec-⊢psx-dim {nil} n _ _ _ _ = inr λ{((x , A) , (Γ⊢psx , (idp , _))) → ∅-is-not-ps _ _ Γ⊢psx}
  dec-⊢psx-dim {Γ@(nil :: (O , ∗))} O O _ _ _ = inl ((0 , ∗) , (pss , (idp , idp)))
  dec-⊢psx-dim {Γ@(nil :: (O , ∗))} O (S n) _ _ _ = inr λ {(_ , (Γ⊢psx , (p , idp))) → Sn≠0 _ (𝔻0-var _ _ (psvar Γ⊢psx))}
  dec-⊢psx-dim {Γ@(nil :: (O , ∗))} (S n) _ _ _ _ = inr λ {(_ , (Γ⊢psx , (p , idp))) → Sn≠0 _ (p ^ >> ap dim (𝔻0-type _ _ (psvar Γ⊢psx)))}
  dec-⊢psx-dim {Γ@(nil :: (O , ⇒ _ _ _))} n _ _ _ _ = inr λ {(_ , (Γ⊢psx , (p , idp))) → ill-formed-1st-type (psv Γ⊢psx)}
  dec-⊢psx-dim {Γ@(nil :: (S y , B))} n _ _ _ _ = inr λ {(_ , (Γ⊢psx , (p , idp))) → ill-formed-1st-var (psv Γ⊢psx)}
  dec-⊢psx-dim {(Γ :: (y , B)) :: (z , ∗)} n _ _ _ _ = inr λ {(_ , (Γ⊢psx , (p , idp))) → ⇒≠∗ (snd (fst (fst (ps-carrier Γ⊢psx)))) }
  dec-⊢psx-dim {Γ++@((Γ :: (y , B)) :: (z , ⇒ C (Var a) (Var b)))} n m ε 0 idp = inr λ {((x , A) , (Γ⊢ps , (dimA , idp))) → ps-not-0 (λ{()}) Γ⊢ps idp}
  dec-⊢psx-dim {Γ++@((Γ :: (y , B)) :: (z , ⇒ C (Var a) (Var b)))} n m (⋖T {y = c} 0⋖c c⋖m) (S l) Sl= with eqdecℕ y (length Γ) | eqdecℕ z (S (length Γ)) | eqdec-PreTy B C | eqdecℕ y b
  ... | inr y≠l | _ | _ | _ = inr λ (_ , (Γ+⊢ps , _)) → y≠l (snd (fst (ps-carrier Γ+⊢ps)))
  ... | inl idp | inr z≠Sl | _ | _ = inr λ (_ , (Γ+⊢ps , _)) → z≠Sl (snd (ps-carrier Γ+⊢ps))
  ... | inl idp | inl idp | inr B≠C | _ = inr λ (_ , (Γ+⊢ps , _)) → B≠C (fst (fst (=⇒ (snd (fst (fst (ps-carrier Γ+⊢ps)))))))
  ... | inl idp | inl idp | inl idp | inr y≠b = inr λ (_ , (Γ+⊢ps , _)) → y≠b (=Var (snd (=⇒ (snd (fst (fst (ps-carrier Γ+⊢ps)))))))
  ... | inl idp | inl idp | inl idp | inl idp with eqdecℕ n (S (dim B)) | eqdecℕ m (S (length Γ)) | eqdecℕ c a
  ... | inl idp | inr m≠SlΓ | _ = inr λ {(_ ,(Γ⊢psa , (d , idp))) → m≠SlΓ (last-var-ps Γ⊢psa d)}
  ... | inl idp | inl idp | inr c≠a = inr λ {((_ , _) ,(Γ⊢psa , (p , idp))) → c≠a (⋖-prev-ps Γ⊢psa c⋖m (⊢ps⋖-∂⁻ (transport {B = λ A → _ ⊢ps _ # A} (unique-type (psvar Γ⊢psa) (var (psv Γ⊢psa) (inr (idp , idp))) idp) Γ⊢psa))) }
  ... | inl idp | inl idp | inl idp with dec-⊢psx-dim {Γ} (dim B) a (strengthen-⋖ 0⋖c) l ((S-is-inj _ _ Sl=) >> (ℓ-strengthen 0⋖c))
  ... | inr Γ⊬ps = inr λ {(_ , (Γ+⊢ps , (p , idp))) → Γ⊬ps (_ , (Γ+⊢ps→Γ⊢ps Γ+⊢ps , (idp , idp)))}
  ... | inl ((_ , D) , (Γ⊢psx , (dimB , idp)))  with eqdec-PreTy B D
  ... | inr B≠D = inr λ {(_ ,(Γ⊢psa , (d , idp))) → B≠D (Γ⊢psx-dim-ty (Γ+⊢ps→Γ⊢ps Γ⊢psa) Γ⊢psx (dimB ^))}
  ... | inl idp = inl ((z , ⇒ C (Var a) (Var b)) , (pse Γ⊢psx idp idp idp idp idp , (idp , idp)))
  dec-⊢psx-dim {Γ++@((Γ :: (y , B)) :: (z , ⇒ C (Var a) (Var b)))} n m (⋖T 0⋖z z⋖m) (S l) Sl= | inl idp | inl idp | inl idp | inl idp | inr n≠SdimB | _ | _ with dec-⊢psx-dim {Γ++} (S n) _ 0⋖z l (S-is-inj _ _ Sl=)
  ... | inl ((f , ⇒ A (Var _) (Var x)) , (Γ⊢psf , (dimA , idp))) = inl ((x , A) , (psd Γ⊢psf , (S-is-inj _ _ dimA , ⋖-next-ps Γ⊢psf (⊢ps⋖ Γ⊢psf) z⋖m)))
  ... | inr ¬∃f = inr λ{((x , A) , (psd Γ⊢psf , (dimA , idp))) → ¬∃f ((_ , _) , (Γ⊢psf , (ap S dimA , ⋖-prev-ps Γ⊢psf (⊢ps⋖ Γ⊢psf) z⋖m)));
                        ((x , A) , ((pse _ _ _ _ idp idp) , (dimB=n , _))) → n≠SdimB (dimB=n ^)}

  -- dec-tgt : ∀ {Γ x A} → dec (Σ (ℕ × ℕ) (λ (a , f) → Γ ⊢t Var f # ⇒ A (Var a) (Var x)))
  -- dec-tgt = {!!}

  -- dec-tgt-ps : ∀ {Γ x a f A} → (Γ⊢ps : Γ ⊢ps f # ⇒ A (Var a) (Var x)) → dec-tgt {Γ} {x} {A} == inl ((a , f) , (psvar Γ⊢ps))
  -- dec-tgt-ps = {!!}

  -- dec-aux : ∀ {Γ x a f A b g val} → (Γ⊢ps : Γ ⊢ps f # ⇒ A (Var a) (Var x)) → inl ((b , g) , val) == dec-tgt {Γ} {x} {A} → Γ ⊢ps g # ⇒ A (Var b) (Var x)
  -- dec-aux = {!!}

  -- dec-⊢psx : ∀ Γ x A → dec (Γ ⊢ps x # A)
  -- dec-⊢psx-aux : ∀ Γ x A y B z C maj → x ≤ maj → dec (((Γ :: (y , B)) :: (z , C)) ⊢ps x # A)

  -- dec-⊢psx nil x A = inr λ{∅⊢psx → ∅-is-not-ps x A ∅⊢psx}
  -- dec-⊢psx Γ@(nil :: (n , ⇒ _ _ _)) x A with dec-⊢C Γ
  -- ... | inr ¬Γ⊢ = inr λ Γ⊢ps → ¬Γ⊢ (psv Γ⊢ps)
  -- ... | inl (cc _ ∅⊢⇒ idp) with ∅-⊢T _ ∅⊢⇒
  -- ... | ()
  -- dec-⊢psx (nil :: (O , ∗)) x A with eqdecℕ O x | eqdec-PreTy ∗ A
  -- ... | inl idp | inl idp = inl pss
  -- ... | inl idp | inr A≠∗ = inr λ {Γ⊢ps0 → A≠∗ (unique-type (var (psv Γ⊢ps0) (inr (idp , idp))) (psvar Γ⊢ps0) idp)}
  -- ... | inr x≠0 | _ = inr λ{Γ⊢psx → x≠0 ((𝔻0-var x A (psvar Γ⊢psx)) ^)}
  -- dec-⊢psx Γ@(nil :: (S n , ∗)) x A with dec-⊢C Γ
  -- ... | inl (cc Γ⊢ x₁ ())
  -- ... | inr ¬Γ⊢ = inr λ Γ⊢ps → ¬Γ⊢ (psv Γ⊢ps)
  -- dec-⊢psx ((Γ :: (y , B)) :: (z , C)) x A with C
  -- ... | ∗ = inr (λ Γ⊢ps → ¬ps-carrier (λ _ → λ{()}) Γ⊢ps)
  -- ... | ⇒ B' (Var a) (Var y') with eqdec-PreTy B B' | eqdecℕ y y'
  -- ... | inl idp | inr y≠y' = inr (λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → y≠y' (=Var (snd (=⇒ eq)) ^)) Γ⊢ps)
  -- ... | inr B≠B' | _ = inr λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → B≠B' (fst (fst (=⇒ eq)) ^)) Γ⊢ps
  -- ... | inl idp | inl idp with dec-≤ (dim A) (S (dim B'))
  -- ... | inl dimA≤SdimB = dec-⊢psx-aux Γ _ _ _ _ _ _ {!!} {!!}
  -- ... | inr abs = inr {!!}

  -- dec-⊢psx-aux Γ .0 A y B z C O (0≤ .0) = inr {!!}
  -- dec-⊢psx-aux Γ x A y B z C (S n) x≤maj with C
  -- ... | ∗ = inr (λ Γ⊢ps → ¬ps-carrier (λ _ → λ{()}) Γ⊢ps)
  -- ... | ⇒ B' (Var a) (Var y') with eqdec-PreTy B B' | eqdecℕ y y'
  -- ... | inr B≠B' | _ = inr λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → B≠B' (fst (fst (=⇒ eq)) ^)) Γ⊢ps
  -- ... | inl idp | inr y≠y' = inr (λ Γ⊢ps → ¬ps-carrier (λ a → λ eq → y≠y' (=Var (snd (=⇒ eq)) ^)) Γ⊢ps)
  -- ... | inl idp | inl idp with dec-⊢psx Γ a B'
  -- ... | inr ¬Γ⊢ps = inr λ Γ+⊢ps → ¬Γ⊢ps (Γ+⊢ps→Γ⊢ps Γ+⊢ps)
  -- ... | inl Γ⊢ps with eqdecℕ z (S (length Γ)) | eqdecℕ y (length Γ)
  -- ... | inr z≠SlΓ | _ = inr λ Γ+⊢ps → z≠SlΓ (last-ps-var Γ+⊢ps)
  -- ... | inl idp | inr y≠lΓ = inr λ Γ+⊢ps → y≠lΓ (previous-to-last-ps-var Γ+⊢ps)
  -- ... | inl idp | inl idp with eqdecℕ x (S (length Γ))
  -- ... | inr x≠SlΓ with dec-tgt {(Γ :: (length Γ , B')) :: (S (length Γ) , ⇒ B' (Var a) (Var (length Γ)))} {x} {A}
  -- ... | inr ¬tgt = inr λ{(psd Γ⊢ps) → ¬tgt ((_ , _) , (psvar Γ⊢ps));
  --                        (pse Γ⊢ps _ _ _ x=Sl _) → x≠SlΓ (x=Sl ^)}
  -- ... | inl ((b , f) , Γ⊢f) with dec-⊢psx-aux Γ f (⇒ A (Var b) (Var x)) y B z (⇒ B' (Var a) (Var y')) n {!!}
  -- ... | inl Γ⊢psf = inl (psd Γ⊢psf)
  -- ... | inr ¬Γ⊢psf = inr λ{(psd Γ⊢psf) → ¬Γ⊢psf (dec-aux Γ⊢psf {!idp!});
  --                          (pse Γ⊢ps _ _ _ x=Sl _) → x≠SlΓ (x=Sl ^)}
  -- dec-⊢psx-aux Γ x A y B z C maj _ | ⇒ B' (Var a) (Var y') | inl idp | inl idp | inl Γ⊢ps | inl idp | inl idp | inl idp with eqdec-PreTy A (⇒ B' (Var a) (Var y'))
  -- ... | inl idp = inl (pse Γ⊢ps idp idp idp idp idp)
  -- ... | inr A≠⇒ = inr λ Γ+⊢ps → A≠⇒ (unique-type (psvar Γ+⊢ps) (var (psv Γ+⊢ps) (inr (idp , idp))) idp)

  Γ⊢psx→x≤lΓ : ∀ {Γ x A} → Γ ⊢ps x # A → x ≤ length Γ
  Γ⊢psx→x≤lΓ = {!!}

  -- dec-⊢ps-aux : ∀ Γ k → dec (Σ ℕ (λ x → ((Γ ⊢ps x # ∗) × (x ≤ k))))
  -- dec-⊢ps-aux₁ : ∀ {Γ k} → ¬ (Γ ⊢ps S k # ∗) → ¬ (Σ ℕ (λ x → ((Γ ⊢ps x # ∗) × (x ≤ k)))) → ¬ (Σ ℕ (λ x → ((Γ ⊢ps x # ∗) × (x ≤ S k))))
  -- dec-⊢ps-aux Γ O with dec-⊢psx Γ O ∗
  -- ... | inl Γ⊢psO = inl (0 , (Γ⊢psO , n≤n _))
  -- ... | inr ¬Γ⊢psO = inr λ{(.O , (Γ⊢psO , (0≤ O))) → ¬Γ⊢psO Γ⊢psO}
  -- dec-⊢ps-aux Γ (S k) with dec-⊢psx Γ (S k) ∗
  -- ... | inl Γ⊢psx = inl (S k , (Γ⊢psx , n≤n _))
  -- ... | inr ¬Γ⊢psSk with dec-⊢ps-aux Γ k
  -- ... | inl (i , (Γ⊢psi , i≤k)) = inl (i , (Γ⊢psi , n≤m→n≤Sm i≤k))
  -- ... | inr H = inr λ {(i , (Γ⊢psi , i≤Sk)) → dec-⊢ps-aux₁ ¬Γ⊢psSk H (i , (Γ⊢psi , i≤Sk))}
  -- dec-⊢ps-aux₁ ¬Γ⊢psSk H (i , (Γ⊢psi , i≤Sk)) with ≤S _ _ i≤Sk
  -- ... | inl i≤k = H (i , (Γ⊢psi , i≤k))
  -- ... | inr idp = ¬Γ⊢psSk Γ⊢psi

  -- dec-⊢ps : ∀ Γ → dec (Γ ⊢ps)
  -- dec-⊢ps Γ with dec-⊢ps-aux Γ (length Γ)
  -- ... | inl (x , (Γ⊢psx , _)) = inl (ps Γ⊢psx)
  -- ... | inr H = inr λ {(ps {x = x} Γ⊢psx) → H (x , (Γ⊢psx , Γ⊢psx→x≤lΓ Γ⊢psx))}


  last-obj : Pre-Ctx → ℕ
  last-obj nil = 0
  last-obj (Γ :: (x , ∗)) = x
  last-obj (Γ :: (x , ⇒ _ _ _)) = last-obj Γ

  Γ⊢ps→last-obj : ∀ {Γ} → Γ ⊢ps → Γ ⊢ps (last-obj Γ) # ∗
  Γ⊢ps→last-obj = {!!}

  dec-⊢ps : ∀ Γ → dec (Γ ⊢ps)
  dec-⊢ps Γ with dec-⋖ Γ 0 (last-obj Γ)
  ... | inr H = inr {!!}
  ... | inl 0⋖l with dec-⊢psx-dim {Γ} 0 (last-obj Γ) 0⋖l (ℓ 0⋖l) idp
  ... | inr Γ⊬psx = inr λ Γ⊢ps → Γ⊬psx (((last-obj Γ) , ∗) , (Γ⊢ps→last-obj Γ⊢ps , (idp , idp)))
  ... | inl ((_ , ∗) , (Γ⊢psx , (_ , idp))) = inl (ps Γ⊢psx)
