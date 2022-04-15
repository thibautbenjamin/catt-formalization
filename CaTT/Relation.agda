{-# OPTIONS --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Uniqueness-Derivations
open import Sets ℕ eqdecℕ
open import GSeTT.Dec-Type-Checking
open import CaTT.Ps-contexts

{- PS-contexts -}
module CaTT.Relation where

  -- The relation ◃ generating cases
  data _,_◃₀_ Γ x y : Set₁ where
    ◃∂⁻ : ∀{A z} → Γ ⊢t (Var y) # (Var x ⇒[ A ] Var z) → Γ , x ◃₀ y
    ◃∂⁺ : ∀{A z} → Γ ⊢t (Var x) # (Var z ⇒[ A ] Var y) → Γ , x ◃₀ y

  -- Transitive closure : we associate on the right
  data _,_◃_ Γ x y : Set₁ where
    gen : Γ , x ◃₀ y → Γ , x ◃ y
    ◃T : ∀{z} → Γ , x ◃ z → Γ , z ◃₀ y → Γ , x ◃ y

  rel : ∀ Γ x y → Set₁
  rel Γ x y = Γ , x ◃ y

  W◃₀ : ∀ {Γ x y z A} → Γ ∙ z # A ⊢C → Γ , x ◃₀ y → Γ ∙ z # A , x ◃₀ y
  W◃₀ Γ+⊢ (◃∂⁻ Γ⊢x) = ◃∂⁻ (wkt Γ⊢x Γ+⊢)
  W◃₀ Γ+⊢ (◃∂⁺ Γ⊢x) = ◃∂⁺ (wkt Γ⊢x Γ+⊢)

  W◃ : ∀ {Γ x y z A} → Γ ∙ z # A ⊢C → Γ , x ◃ y → Γ ∙ z # A , x ◃ y
  W◃ Γ+⊢ (gen x◃₀y) = gen (W◃₀ Γ+⊢ x◃₀y)
  W◃ Γ+⊢ (◃T x◃y y◃₀z) = ◃T (W◃ Γ+⊢ x◃y) (W◃₀ Γ+⊢ y◃₀z)

  WW◃ : ∀ {Γ x y z f A B} → ((Γ ∙ z # A) ∙ f # B) ⊢C → Γ , x ◃ y → ((Γ ∙ z # A) ∙ f # B) , x ◃ y
  WW◃ Γ+⊢@(cc Γ⊢ _ idp) x◃y = W◃ Γ+⊢ (W◃ Γ⊢ x◃y)

  ◃-trans : ∀ {Γ x y z} → Γ , x ◃ y → Γ , y ◃ z → Γ , x ◃ z
  ◃-trans x◃y (gen y◃₀z) = ◃T x◃y y◃₀z
  ◃-trans x◃y (◃T y◃z z◃₀w) = ◃T (◃-trans x◃y y◃z) z◃₀w

  -- TODO : Move at the right place
  x#A∈Γ→x∈Γ : ∀ {Γ x A} → x # A ∈ Γ → x ∈ Γ
  x#A∈Γ→x∈Γ {Γ ∙ y # _} (inl x#A∈Γ) = inl (x#A∈Γ→x∈Γ x#A∈Γ)
  x#A∈Γ→x∈Γ {Γ ∙ y # _} (inr (idp , idp)) = inr idp

  Γ⊢x:A→x∈Γ : ∀ {Γ x A} → Γ ⊢t (Var x) # A → x ∈ Γ
  Γ⊢x:A→x∈Γ (var _ x#A∈Γ) = x#A∈Γ→x∈Γ x#A∈Γ

  data _,_⟿_ : Pre-Ctx → ℕ → ℕ → Set₁ where -- y is an iterated target of x in Γ
    ∂⁺⟿ : ∀{Γ x a y A} → Γ ⊢t (Var x) # (Var a ⇒[ A ] Var y) → Γ , x ⟿ y
    x⟿∂⁺ : ∀{Γ x a y z A} → Γ ⊢t (Var x) # (Var a ⇒[ A ] Var y) → Γ , y ⟿ z → Γ , x ⟿ z

  W⟿ : ∀ {Γ x y z A} → (Γ ∙ z # A) ⊢C → Γ , x ⟿ y → (Γ ∙ z # A) , x ⟿ y
  W⟿ Γ+⊢ (∂⁺⟿ Γ⊢x) = ∂⁺⟿ (wkt Γ⊢x Γ+⊢)
  W⟿ Γ+⊢ (x⟿∂⁺ Γ⊢x x⟿y) = x⟿∂⁺ (wkt Γ⊢x Γ+⊢) (W⟿ Γ+⊢ x⟿y)

  WW⟿ : ∀ {Γ x y z w A B} → (Γ ∙ z # A) ∙ w # B ⊢C → Γ , x ⟿ y → (Γ ∙ z # A) ∙ w # B , x ⟿ y
  WW⟿ Γ++⊢@(cc Γ+⊢ _ idp) x⟿y = W⟿ Γ++⊢ (W⟿ Γ+⊢ x⟿y)

  ⟿→◃ : ∀ {Γ x y} → Γ , x ⟿ y → Γ , x ◃ y
  ⟿→◃ (∂⁺⟿ Γ⊢x) = gen (◃∂⁺ Γ⊢x)
  ⟿→◃ (x⟿∂⁺ Γ⊢x x⟿y) = ◃-trans (gen (◃∂⁺ Γ⊢x)) (⟿→◃ x⟿y)

  Γ++ : ∀ {Γ x A} → Γ ⊢ps x # A → Pre-Ctx
  Γ++ {Γ} {x} {A} _ = (Γ ∙ ℓ Γ # A) ∙ S (ℓ Γ) # Var x ⇒[ A ] Var (ℓ Γ)

  //⟿ : ∀ {Γ Δ x y A a} → Γ ⊢t (Var x) # A → Δ ⊢t (Var y) # A → Γ , x ⟿ a → Δ , y ⟿ a
  //⟿ Γ⊢x Δ⊢y (∂⁺⟿ Γ⊢x') with unique-type Γ⊢x Γ⊢x' idp
  ... | idp = ∂⁺⟿ Δ⊢y
  //⟿ Γ⊢x Δ⊢y (x⟿∂⁺ Γ⊢x' x⟿a) with unique-type Γ⊢x Γ⊢x' idp
  ... | idp = x⟿∂⁺ Δ⊢y (//⟿ (Γ⊢tgt (Γ⊢t:A→Γ⊢A Γ⊢x)) (Γ⊢tgt (Γ⊢t:A→Γ⊢A Δ⊢y)) x⟿a)

  T⟿ : ∀ {Γ x y z} → Γ , x ⟿ y → Γ , y ⟿ z → Γ , x ⟿ z
  T⟿ (∂⁺⟿ Γ⊢x) y⟿z = x⟿∂⁺ Γ⊢x y⟿z
  T⟿ (x⟿∂⁺ Γ⊢x x⟿y) y⟿z = x⟿∂⁺ Γ⊢x (T⟿ x⟿y y⟿z)

  ⟿dim : ∀ {Γ x y A B} → Γ ⊢t Var x # A → Γ ⊢t Var y # B → Γ , x ⟿ y → dim B < dim A
  ⟿dim Γ⊢x:A Γ⊢y:B (∂⁺⟿ Γ⊢x) with unique-type Γ⊢x:A Γ⊢x idp | unique-type Γ⊢y:B (Γ⊢tgt(Γ⊢t:A→Γ⊢A Γ⊢x)) idp
  ... | idp | idp = n≤n _
  ⟿dim Γ⊢x:A Γ⊢y:B (x⟿∂⁺ Γ⊢x z⟿y) with unique-type Γ⊢x:A Γ⊢x idp
  ... | idp = n≤m→n≤Sm (⟿dim (Γ⊢tgt(Γ⊢t:A→Γ⊢A Γ⊢x)) Γ⊢y:B z⟿y)


  𝔻0-◃ : ∀ z → ¬ ((∅ ∙ 0 # ∗) , 0 ◃ z)
  𝔻0-◃ z (gen (◃∂⁻ (var _ (inl ()))))
  𝔻0-◃ z (gen (◃∂⁻ (var _ (inr ()))))
  𝔻0-◃ z (gen (◃∂⁺ (var _ (inl ()))))
  𝔻0-◃ z (gen (◃∂⁺ (var _ (inr ()))))
  𝔻0-◃ z (◃T 0◃x _) = 𝔻0-◃ _ 0◃x

  𝔻0-⟿ : ∀ z → ¬ ((∅ ∙ 0 # ∗) , 0 ⟿ z)
  𝔻0-⟿ z (∂⁺⟿ (var _ (inl ())))
  𝔻0-⟿ z (∂⁺⟿ (var _ (inr ())))
  𝔻0-⟿ z (x⟿∂⁺ (var _ (inl ())) _)
  𝔻0-⟿ z (x⟿∂⁺ (var _ (inr ())) _)

  n≮n : ∀ n → ¬ (n < n)
  n≮n n n<n = Sn≰n _ n<n

  ⟿-is-tgt : ∀ {Γ x y z A} → Γ ⊢t Var x # Var y ⇒[ A ] Var z → Γ , x ⟿ y → y == z
  ⟿-is-tgt Γ⊢x (∂⁺⟿ Γ⊢'x) with unique-type Γ⊢x Γ⊢'x idp
  ... | idp = idp
  ⟿-is-tgt Γ⊢x (x⟿∂⁺ Γ⊢'x y'⟿y) with unique-type Γ⊢x Γ⊢'x idp
  ... | idp = ⊥-elim (Sn≰n _ (⟿dim (Γ⊢tgt (Γ⊢t:A→Γ⊢A Γ⊢'x)) (Γ⊢src (Γ⊢t:A→Γ⊢A Γ⊢x)) y'⟿y))

  no-loop : ∀{Γ x y z T a A} → Γ ⊢ps a # A → Γ ⊢t Var x # Var y ⇒[ T ] Var z → y ≠ z
  no-loop pss (var _ (inl ())) idp
  no-loop pss (var _ (inr ())) idp
  no-loop (psd Γ⊢psf) Γ⊢x idp = no-loop Γ⊢psf Γ⊢x idp
  no-loop (pse Γ⊢psb idp idp idp idp idp) (var _ (inl (inl x∈Γ))) idp = no-loop Γ⊢psb (var (Γ⊢psx:A→Γ⊢ Γ⊢psb) x∈Γ) idp
  no-loop (pse Γ⊢psb idp idp idp idp idp) (var _ (inl (inr (idp , idp)))) idp = no-loop Γ⊢psb (Γ⊢psx:A→Γ⊢x:A Γ⊢psb) idp
  no-loop (pse Γ⊢psb idp idp idp idp idp) (var _ (inr (idp , idp))) idp = x∉ (Γ⊢psx:A→Γ⊢ Γ⊢psb) (n≤n _) (Γ⊢psx:A→Γ⊢x:A Γ⊢psb)

  dangling-is-not-a-source : ∀ {Γ x A} → Γ ⊢ps x # A → (∀ f z {B} →  ¬ (Γ ⊢t Var f # Var x ⇒[ B ] Var z))
  post-dangling-is-not-a-source : ∀ {Γ x A} → Γ ⊢ps x # A → (∀ {y B} f z → Γ , x ⟿ y →  ¬ (Γ ⊢t (Var f) # Var y ⇒[ B ] Var z))

  dangling-is-not-a-source pss _ _ (var _ (inl ()))
  dangling-is-not-a-source pss _ _ (var _ (inr ()))
  dangling-is-not-a-source {x = x} (psd Γ⊢ps) t u Γ⊢t = post-dangling-is-not-a-source Γ⊢ps t u  (∂⁺⟿ (psvar Γ⊢ps)) Γ⊢t
  dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (var _ (inl (inl x∈Γ))) = x∉ (psv Γ⊢ps) (n≤Sn _) (Γ⊢src (Γ⊢t:A→Γ⊢A (var (psv Γ⊢ps) x∈Γ)))
  dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (var _ (inl (inr (idp , idp)))) = x∉ (psv Γ⊢ps) (n≤Sn _) (Γ⊢src (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps)))
  dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (var _ (inr (idp , idp))) = x∉ (psv Γ⊢ps) (n≤Sn _) (psvar Γ⊢ps)
  post-dangling-is-not-a-source pss t u x⟿y Γ⊢t = 𝔻0-⟿ _ x⟿y
  post-dangling-is-not-a-source (psd Γ⊢ps) t u x⟿y Γ⊢t = post-dangling-is-not-a-source Γ⊢ps t u (T⟿ (∂⁺⟿ (psvar Γ⊢ps)) x⟿y) Γ⊢t
  post-dangling-is-not-a-source Γ+⊢@(pse Γ⊢ps idp idp idp idp idp) t u (∂⁺⟿ Γ⊢Sl) Γ⊢t with unique-type Γ⊢Sl (psvar Γ+⊢) idp
  post-dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (∂⁺⟿ Γ⊢Sl) (var _ (inl (inl t∈Γ))) | idp = x∉ (psv Γ⊢ps) (n≤n _) (Γ⊢src (Γ⊢t:A→Γ⊢A (var (psv Γ⊢ps) t∈Γ)))
  post-dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (∂⁺⟿ Γ⊢Sl) (var _ (inl (inr (idp , idp)))) | idp = x∉ (psv Γ⊢ps) (n≤n _) (Γ⊢src (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps)))
  post-dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (∂⁺⟿ Γ⊢Sl) (var _ (inr (idp , idp))) | idp = x∉ (psv Γ⊢ps) (n≤n _) (psvar Γ⊢ps)
  post-dangling-is-not-a-source Γ+⊢@(pse Γ⊢ps idp idp idp idp idp) t u (x⟿∂⁺ Γ⊢Sl x⟿y) Γ⊢t with unique-type Γ⊢Sl (psvar Γ+⊢) idp
  post-dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (x⟿∂⁺ Γ⊢Sl x⟿y) (var Γ+⊢ (inl (inl t∈Γ))) | idp =
         post-dangling-is-not-a-source Γ⊢ps _ _ (//⟿ (var Γ+⊢ (inl (inr (idp , idp)))) (psvar Γ⊢ps) x⟿y) (var (psv Γ⊢ps) t∈Γ)
  post-dangling-is-not-a-source (pse Γ⊢ps  idp idp idp idp idp)  _ _ (x⟿∂⁺ Γ⊢Sl x⟿y) (var Γ+⊢ (inl (inr (idp , idp)))) | idp with ⟿-is-tgt (var Γ+⊢ (inl (inr (idp , idp)))) x⟿y
  ... | idp = no-loop Γ⊢ps (psvar Γ⊢ps) idp
  post-dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (x⟿∂⁺ Γ⊢Sl x⟿y) (var Γ++⊢@(cc Γ+⊢ _ p) (inr (idp , idp))) | idp = n≮n _ (⟿dim (var Γ++⊢ (inl (inr (idp , idp)))) (wkt (wkt (psvar Γ⊢ps) Γ+⊢) Γ++⊢) x⟿y)

  ⊢psx-◃₀→⟿ : ∀ {Γ x a A} → Γ ⊢ps x # A → Γ , x ◃₀ a → Γ , x ⟿ a
  ⊢psx-◃₀→⟿ Γ⊢psx (◃∂⁻ Γ⊢a) = ⊥-elim (dangling-is-not-a-source Γ⊢psx _ _ Γ⊢a)
  ⊢psx-◃₀→⟿ Γ⊢psx (◃∂⁺ Γ⊢x) = ∂⁺⟿ Γ⊢x

  ⊢psx-◃₀→⟿+ : ∀ {Γ x y a A} → Γ ⊢ps x # A → Γ , x ⟿ y → Γ , y ◃₀ a → Γ , y ⟿ a
  ⊢psx-◃₀→⟿+ Γ⊢psx x⟿y (◃∂⁻ Γ⊢a) = ⊥-elim (post-dangling-is-not-a-source Γ⊢psx _ _ x⟿y Γ⊢a)
  ⊢psx-◃₀→⟿+ Γ⊢psx x⟿y (◃∂⁺ Γ⊢y) = ∂⁺⟿ Γ⊢y

  ⊢psx-◃→⟿ : ∀ {Γ x a A} → Γ ⊢ps x # A → Γ , x ◃ a → Γ , x ⟿ a
  ⊢psx-◃→⟿+ : ∀ {Γ x a b A} → Γ ⊢ps x # A → Γ , x ⟿ a → Γ , a ◃ b → Γ , a ⟿ b

  ⊢psx-◃→⟿ Γ⊢psx (gen x◃₀a) = ⊢psx-◃₀→⟿ Γ⊢psx x◃₀a
  ⊢psx-◃→⟿ Γ⊢psx (◃T x◃z z◃₀a) = T⟿ (⊢psx-◃→⟿ Γ⊢psx x◃z) (⊢psx-◃₀→⟿+ Γ⊢psx (⊢psx-◃→⟿ Γ⊢psx x◃z) z◃₀a)
  ⊢psx-◃→⟿+ Γ⊢psx x⟿y (gen y◃₀a) = ⊢psx-◃₀→⟿+ Γ⊢psx x⟿y y◃₀a
  ⊢psx-◃→⟿+ Γ⊢psx x⟿y (◃T y◃z z◃₀a) = T⟿ (⊢psx-◃→⟿+ Γ⊢psx x⟿y y◃z) (⊢psx-◃₀→⟿+ Γ⊢psx (T⟿ x⟿y (⊢psx-◃→⟿+ Γ⊢psx x⟿y y◃z)) z◃₀a)

  -- easy to finish, and follows the paper proof
  psx-◃-linear→ : ∀ {Γ x A} → Γ ⊢ps x # A → (∀ a b → a ∈ Γ → b ∈ Γ → (((Γ , a ◃ b) + (Γ , b ◃ a)) + (a == b)))
  psx-◃-linear→ pss .0 .0 (inr idp) (inr idp) = inr idp
  psx-◃-linear→ (psd Γ⊢psx) a b a∈Γ b∈Γ = psx-◃-linear→ Γ⊢psx a b a∈Γ b∈Γ
  psx-◃-linear→ Γ++⊢ps@(pse Γ⊢psx idp idp idp idp idp) a b (inl (inl a∈Γ)) (inl (inl b∈Γ)) with psx-◃-linear→ Γ⊢psx a b a∈Γ b∈Γ
  ... | inl (inl a◃b) = inl (inl (WW◃ (psv Γ++⊢ps) a◃b))
  ... | inl (inr b◃a) = inl (inr (WW◃ (psv Γ++⊢ps) b◃a))
  ... | inr idp = inr idp
  psx-◃-linear→ Γ++⊢ps@(pse {x = x} Γ⊢psx idp idp idp idp idp) a .(ℓ _) (inl (inl a∈Γ)) (inl (inr idp)) with psx-◃-linear→ Γ⊢psx a x a∈Γ (Γ⊢x:A→x∈Γ (psvar Γ⊢psx)) -- a ∈ Γ , b = y
  ... | inl (inl a◃x) = inl (inl (◃-trans (WW◃ (psv Γ++⊢ps) a◃x) (◃T (gen (◃∂⁻ (psvar Γ++⊢ps))) ((◃∂⁺ (psvar Γ++⊢ps)))))) -- a ◃ x
  ... | inl (inr x◃a) = inl (inr (⟿→◃ (//⟿ (psvar Γ⊢psx) (var (psv Γ++⊢ps) (inl (inr (idp , idp)))) (⊢psx-◃→⟿ Γ⊢psx x◃a)))) -- x ◃ a
  ... | inr idp = inl (inl (◃T (gen (◃∂⁻ (psvar Γ++⊢ps))) (◃∂⁺ (psvar Γ++⊢ps)))) -- a = x
  psx-◃-linear→ Γ++⊢ps@(pse {x = x} Γ⊢psx idp idp idp idp idp) a .(S (ℓ _)) (inl (inl a∈Γ)) (inr idp) with psx-◃-linear→ Γ⊢psx a x a∈Γ (Γ⊢x:A→x∈Γ (psvar Γ⊢psx)) -- a ∈ Γ , b = f (**)
  ... | inl (inl a◃x) = inl (inl (◃T (WW◃ (psv Γ++⊢ps) a◃x) (◃∂⁻ (psvar Γ++⊢ps)))) -- a ◃ x
  ... | inl (inr x◃a) = inl (inr (⟿→◃ (x⟿∂⁺ (psvar Γ++⊢ps) (//⟿ (psvar Γ⊢psx) (var (psv Γ++⊢ps) (inl (inr (idp , idp)))) (⊢psx-◃→⟿ Γ⊢psx x◃a))))) -- x ◃ a
  ... | inr idp = inl (inl (gen (◃∂⁻ (psvar Γ++⊢ps)))) -- a = x
  psx-◃-linear→ Γ++⊢ps@(pse {x = x} Γ⊢psx idp idp idp idp idp) .(ℓ _) b (inl (inr idp)) (inl (inl b∈Γ)) with psx-◃-linear→ Γ⊢psx b x b∈Γ (Γ⊢x:A→x∈Γ (psvar Γ⊢psx)) -- a = y, b ∈ Γ
  ... | inl (inl b◃x) = inl (inr (◃-trans (WW◃ (psv Γ++⊢ps) b◃x) (◃T (gen (◃∂⁻ (psvar Γ++⊢ps))) (◃∂⁺ (psvar Γ++⊢ps))))) -- b ◃ x
  ... | inl (inr x◃b) = inl (inl (⟿→◃ (//⟿ (psvar Γ⊢psx) (var (psv Γ++⊢ps) (inl (inr (idp , idp)))) (⊢psx-◃→⟿ Γ⊢psx x◃b)))) -- x ◃ b
  ... | inr idp = inl (inr (◃T (gen (◃∂⁻ (psvar Γ++⊢ps))) (◃∂⁺ (psvar Γ++⊢ps)))) -- b = x
  psx-◃-linear→ (pse Γ⊢psx idp idp idp idp idp) .(ℓ _) .(ℓ _) (inl (inr idp)) (inl (inr idp)) = inr idp
  psx-◃-linear→ Γ++⊢ps@(pse Γ⊢psx idp idp idp idp idp) .(ℓ _) .(S (ℓ _)) (inl (inr idp)) (inr idp) = inl (inr (gen (◃∂⁺ (psvar Γ++⊢ps)))) -- a = y, b = f
  psx-◃-linear→ Γ++⊢ps@(pse {x = x} Γ⊢psx  idp idp idp idp idp) .(S (ℓ _)) b (inr idp) (inl (inl b∈Γ)) with psx-◃-linear→ Γ⊢psx b x b∈Γ (Γ⊢x:A→x∈Γ (psvar Γ⊢psx)) -- a = f b ∈ Γ
  ... | inl (inl b◃x) = inl (inr (◃T (WW◃ (psv Γ++⊢ps) b◃x) (◃∂⁻ (psvar Γ++⊢ps)))) -- b ◃ x
  ... | inl (inr x◃b) = inl (inl (⟿→◃ (x⟿∂⁺ (psvar Γ++⊢ps) (//⟿ (psvar Γ⊢psx) (var (psv Γ++⊢ps) (inl (inr (idp , idp)))) (⊢psx-◃→⟿ Γ⊢psx x◃b)))))  -- x ◃ b
  ... | inr idp = inl (inr (gen (◃∂⁻ (psvar Γ++⊢ps)))) -- b = x
  psx-◃-linear→ Γ++⊢ps@(pse Γ⊢psx idp idp idp idp idp) .(S (ℓ _)) .(ℓ _) (inr idp) (inl (inr idp)) = inl (inl (gen (◃∂⁺ (psvar Γ++⊢ps)))) -- a = f, b = y
  psx-◃-linear→ (pse Γ⊢psx idp idp idp idp idp) .(S (ℓ _)) .(S (ℓ _)) (inr idp) (inr idp) = inr idp

  strengthen : ∀ {Γ x A y B} → Γ ∙ y # B ⊢t Var x # A → x ∈ Γ → Γ ⊢t Var x # A
  strengthen (var (cc Γ⊢ _ idp) (inl x#A∈Γ)) x∈Γ = var Γ⊢ x#A∈Γ
  strengthen (var (cc Γ⊢ _ idp) (inr (idp , idp))) x∈Γ = ⊥-elim (l∉ Γ⊢ (n≤n _) x∈Γ)

  strengthen+ : ∀ {Γ x A y B z C} → (Γ ∙ y # B) ∙ z # C ⊢t Var x # A → x ∈ Γ → Γ ⊢t Var x # A
  strengthen+ Γ++⊢x x∈Γ = strengthen (strengthen Γ++⊢x (inl x∈Γ)) x∈Γ

  ◃₀∈ : ∀ {Γ x a} → Γ , x ◃₀ a → a ∈ Γ
  ◃₀∈ (◃∂⁻ Γ⊢a) = Γ⊢x:A→x∈Γ Γ⊢a
  ◃₀∈ (◃∂⁺ Γ⊢x) = Γ⊢x:A→x∈Γ (Γ⊢tgt (Γ⊢t:A→Γ⊢A Γ⊢x))

  ◃∈ : ∀ {Γ x a} → Γ , x ◃ a → a ∈ Γ
  ◃∈ (gen x◃₀a) = ◃₀∈ x◃₀a
  ◃∈ (◃T _ z◃₀x) = ◃₀∈ z◃₀x

  ∈◃₀ : ∀ {Γ x a} → Γ , x ◃₀ a → x ∈ Γ
  ∈◃₀ (◃∂⁻ Γ⊢a) = Γ⊢x:A→x∈Γ (Γ⊢src (Γ⊢t:A→Γ⊢A Γ⊢a))
  ∈◃₀ (◃∂⁺ Γ⊢x) = Γ⊢x:A→x∈Γ Γ⊢x

  ∈◃ : ∀ {Γ x a} → Γ , x ◃ a → x ∈ Γ
  ∈◃ (gen x◃₀a) = ∈◃₀ x◃₀a
  ∈◃ (◃T x◃z _) = ∈◃ x◃z


  WWpsx : ∀ {Γ x A} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps ⊢t (Var x) # A
  WWpsx Γ⊢ps = wkt (wkt (psvar Γ⊢ps) (cc (psv Γ⊢ps) (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps)) idp)) (psv (pse Γ⊢ps idp idp idp idp idp))

  dangling-◃₀ : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , S (ℓ Γ) ◃₀ a → a == ℓ Γ
  dangling-◃₀ Γ⊢ps (◃∂⁻ Γ⊢a) = ⊥-elim (dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ Γ⊢a)
  dangling-◃₀ Γ⊢ps (◃∂⁺ (var _ (inl (inl Sl∈Γ)))) = ⊥-elim (l∉ (psv Γ⊢ps) (n≤Sn _) (x#A∈Γ→x∈Γ Sl∈Γ))
  dangling-◃₀ Γ⊢ps (◃∂⁺ (var _ (inl (inr (Sl=l , idp))))) = ⊥-elim (Sn≠n _ Sl=l)
  dangling-◃₀ Γ⊢ps (◃∂⁺ (var _ (inr (_ , idp)))) = idp

  ◃₀-dangling : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , a ◃₀ S (ℓ Γ)  → a == x
  ◃₀-dangling Γ⊢ps (◃∂⁻ Γ+⊢Sl) with unique-type Γ+⊢Sl (psvar (pse Γ⊢ps idp idp idp idp idp)) idp
  ... | idp = idp
  ◃₀-dangling Γ⊢ps (◃∂⁺ (var x (inl (inl a∈Γ)))) = ⊥-elim (x∉ (psv Γ⊢ps) (n≤Sn _) (Γ⊢tgt (Γ⊢t:A→Γ⊢A (var (psv Γ⊢ps) a∈Γ))))
  ◃₀-dangling Γ⊢ps (◃∂⁺ (var x (inl (inr (idp , idp))))) = ⊥-elim (x∉ (psv Γ⊢ps) (n≤Sn _) (Γ⊢tgt (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps))))
  ◃₀-dangling Γ⊢ps (◃∂⁺ (var x (inr (idp , abs)))) = ⊥-elim (Sn≠n _ (=Var (snd (=⇒ abs))))

  ◃₀-dangling-tgt : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , a ◃₀ ℓ Γ  → (a == S (ℓ Γ)) + (Γ++ Γ⊢ps , a ◃₀ x)
  ◃₀-dangling-tgt Γ⊢ps (◃∂⁻ Γ+⊢l) with unique-type Γ+⊢l (var (psv (pse Γ⊢ps idp idp idp idp idp)) (inl (inr (idp , idp)))) idp
  ... | idp = inr (◃∂⁻ (WWpsx Γ⊢ps))
  ◃₀-dangling-tgt Γ⊢ps (◃∂⁺ (var x (inl (inl a∈Γ)))) = ⊥-elim (x∉ (psv Γ⊢ps) (n≤n _) (Γ⊢tgt (Γ⊢t:A→Γ⊢A (var (psv Γ⊢ps) a∈Γ))))
  ◃₀-dangling-tgt Γ⊢ps (◃∂⁺ (var x (inl (inr (idp , idp))))) = ⊥-elim (x∉ (psv Γ⊢ps) (n≤n _) (Γ⊢tgt (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps))))
  ◃₀-dangling-tgt Γ⊢ps (◃∂⁺ (var x (inr (p , _)))) = inl p

  ◃-dangling : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , a ◃ S (ℓ Γ)  → (a == x) + (Γ++ Γ⊢ps , a ◃ x)
  ◃-dangling Γ⊢ps (gen x◃₀Sl) with ◃₀-dangling Γ⊢ps x◃₀Sl
  ... | idp = inl idp
  ◃-dangling Γ⊢ps (◃T a◃x x◃₀Sl) with ◃₀-dangling Γ⊢ps x◃₀Sl
  ... | idp = inr a◃x

  ◃-dangling-tgt : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , a ◃ ℓ Γ  → (a == S (ℓ Γ) + (a == x)) + (Γ++ Γ⊢ps , a ◃ x)
  ◃-dangling-tgt Γ⊢ps (gen a◃₀l) with ◃₀-dangling-tgt Γ⊢ps a◃₀l
  ... | inl idp = inl (inl idp)
  ... | inr a◃₀x = inr (gen a◃₀x)
  ◃-dangling-tgt Γ⊢ps (◃T a◃z z◃₀l) with ◃₀-dangling-tgt Γ⊢ps z◃₀l
  ... | inl idp with ◃-dangling Γ⊢ps a◃z
  ... | inl idp = inl (inr idp)
  ... | inr a◃x = inr a◃x
  ◃-dangling-tgt Γ⊢ps (◃T a◃z z◃₀l) | inr z◃₀x = inr (◃T a◃z z◃₀x)


  strengthen-◃₀ : ∀ {Γ x A a b} → (Γ⊢ps : Γ ⊢ps x # A) → a ∈ Γ → b ∈ Γ → Γ++ Γ⊢ps , a ◃₀ b → Γ , a ◃₀ b
  strengthen-◃₀ Γ⊢ps a∈Γ b∈Γ (◃∂⁻ Γ⊢b) = ◃∂⁻ (strengthen+ Γ⊢b b∈Γ)
  strengthen-◃₀ Γ⊢ps a∈Γ b∈Γ (◃∂⁺ Γ⊢a) = ◃∂⁺ (strengthen+ Γ⊢a a∈Γ)

  -- useful particular case
  strengthen-◃₀-dangling : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , ℓ Γ ◃₀ a → Γ , x ◃₀ a
  strengthen-◃₀-dangling Γ⊢ps (◃∂⁻ Γ⊢a) = ⊥-elim (post-dangling-is-not-a-source (pse Γ⊢ps idp idp idp idp idp) _ _ (∂⁺⟿ (psvar (pse Γ⊢ps idp idp idp idp idp))) Γ⊢a)
  strengthen-◃₀-dangling Γ⊢ps (◃∂⁺ (var _ (inl (inl l∈Γ)))) = ⊥-elim (l∉ (psv Γ⊢ps) (n≤n _) (x#A∈Γ→x∈Γ l∈Γ))
  strengthen-◃₀-dangling Γ⊢ps (◃∂⁺ (var _ (inl (inr (_ , idp))))) = ◃∂⁺ (psvar Γ⊢ps)
  strengthen-◃₀-dangling Γ⊢ps (◃∂⁺ (var _ (inr (l=Sl , _)))) = ⊥-elim (Sn≠n _ (l=Sl ^))

  ∈-dangling : ∀ {Γ x A} → Γ ⊢ps x # A → x ∈ Γ
  ∈-dangling Γ⊢ps = Γ⊢x:A→x∈Γ (psvar Γ⊢ps)

  ∈-dangling-◃₀ : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , a ◃₀ x → a ∈ Γ
  ∈-dangling-◃₀ Γ⊢ps (◃∂⁻ Γ+⊢x) with unique-type Γ+⊢x  (WWpsx Γ⊢ps) idp
  ... | idp = Γ⊢x:A→x∈Γ (Γ⊢src (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps)))
  ∈-dangling-◃₀ Γ⊢ps (◃∂⁺ (var _ (inl (inl a∈Γ)))) = x#A∈Γ→x∈Γ a∈Γ
  ∈-dangling-◃₀ Γ⊢ps (◃∂⁺ (var _ (inl (inr (idp , idp))))) with unique-type (psvar Γ⊢ps) (Γ⊢tgt (Γ⊢t:A→Γ⊢A (psvar Γ⊢ps))) idp
  ... | ()
  ∈-dangling-◃₀ Γ⊢ps (◃∂⁺ (var _ (inr (idp , idp)))) = ⊥-elim (x∉ (psv Γ⊢ps) (n≤n _) (psvar Γ⊢ps))

  strengthen-dangling-◃₀ : ∀ {Γ x A a} → (Γ⊢ps : Γ ⊢ps x # A) → Γ++ Γ⊢ps , a ◃₀ x → Γ , a ◃₀ x
  strengthen-dangling-◃₀ Γ⊢ps a◃₀x = strengthen-◃₀ Γ⊢ps (∈-dangling-◃₀ Γ⊢ps a◃₀x) (∈-dangling Γ⊢ps) a◃₀x


  -- Not easy to find a way to express in a terminating way
  pse-◃-elim : ∀ {Γ x A a b} → (Γ⊢ps : Γ ⊢ps x # A) → a ∈ Γ → b ∈ Γ → Γ++ Γ⊢ps , a ◃ b → Γ , a ◃ b
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (gen a◃₀b) = gen (strengthen-◃₀ Γ⊢ps a∈Γ b∈Γ a◃₀b)
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T a◃z z◃₀b) with ◃∈ a◃z
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T a◃z z◃₀b) | inl (inl z∈Γ) = ◃T (pse-◃-elim Γ⊢ps a∈Γ z∈Γ a◃z) (strengthen-◃₀ Γ⊢ps z∈Γ b∈Γ z◃₀b)
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T (gen a◃₀l) l◃₀b) | inl (inr idp) with ◃₀-dangling-tgt Γ⊢ps a◃₀l
  ... | inl idp = ⊥-elim (l∉ (psv Γ⊢ps) (n≤Sn _) a∈Γ)
  ... | inr a◃₀x = ◃T (gen (strengthen-◃₀ Γ⊢ps a∈Γ (∈-dangling Γ⊢ps) a◃₀x)) (strengthen-◃₀-dangling Γ⊢ps l◃₀b)
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T (◃T a◃z z◃₀l) l◃₀b) | inl (inr idp) with ◃₀-dangling-tgt Γ⊢ps z◃₀l
  ... | inr z◃₀x = ◃T (◃T (pse-◃-elim Γ⊢ps a∈Γ (∈-dangling-◃₀ Γ⊢ps z◃₀x) a◃z) (strengthen-dangling-◃₀ Γ⊢ps z◃₀x)) (strengthen-◃₀-dangling Γ⊢ps l◃₀b)
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T (◃T (gen a◃₀Sl) Sl◃₀l) l◃₀b) | inl (inr idp) | inl idp with ◃₀-dangling Γ⊢ps a◃₀Sl
  ... | idp = gen (strengthen-◃₀-dangling Γ⊢ps l◃₀b)
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T (◃T (◃T a◃z z◃₀Sl) Sl◃₀l) l◃₀b) | inl (inr idp) | inl idp with ◃₀-dangling Γ⊢ps z◃₀Sl
  ... | idp = ◃T (pse-◃-elim Γ⊢ps a∈Γ (∈-dangling Γ⊢ps) a◃z) (strengthen-◃₀-dangling Γ⊢ps l◃₀b)
  pse-◃-elim Γ⊢ps a∈Γ b∈Γ (◃T a◃z z◃₀b) | inr idp with dangling-◃₀ Γ⊢ps z◃₀b
  ... | idp = ⊥-elim (l∉ (psv Γ⊢ps) (n≤n _) b∈Γ)

  psx-◃-linear← : ∀ {Γ z A} → Γ ⊢ps z # A → (∀ x → x ∈ Γ →  ¬ (Γ , x ◃ x))
  psx-◃-linear← pss .0 (inr idp) x◃x = 𝔻0-◃ 0 x◃x
  psx-◃-linear← (psd Γ⊢psz) x x∈Γ x◃x = psx-◃-linear← Γ⊢psz x x∈Γ x◃x
  psx-◃-linear← (pse Γ⊢psz idp idp idp idp idp) x (inl (inl x∈Γ)) x◃x = psx-◃-linear← Γ⊢psz x x∈Γ (pse-◃-elim Γ⊢psz x∈Γ x∈Γ x◃x)
  psx-◃-linear← Γ+⊢ps@(pse Γ⊢psz idp idp idp idp idp) x (inl (inr idp)) x◃x = ⊥-elim (Sn≰n _ (⟿dim (var (psv Γ+⊢ps) (inl (inr (idp , idp)))) (var (psv Γ+⊢ps) (inl (inr (idp , idp)))) (⊢psx-◃→⟿+ Γ+⊢ps (∂⁺⟿ (psvar Γ+⊢ps)) x◃x)))
  psx-◃-linear← Γ+⊢ps@(pse Γ⊢psz idp idp idp idp idp) x (inr idp) x◃x = ⊥-elim (Sn≰n _ (⟿dim (psvar Γ+⊢ps) (psvar Γ+⊢ps) (⊢psx-◃→⟿ Γ+⊢ps x◃x)))

  ◃-linear : Pre-Ctx → Set₁
  ◃-linear Γ = ∀ x y → x ∈ Γ → y ∈ Γ → (x ≠ y) ↔ ((Γ , x ◃ y) + (Γ , y ◃ x))

  ps-◃-linear : ∀ Γ → Γ ⊢ps → ◃-linear Γ
  fst (ps-◃-linear Γ (ps Γ⊢psz) x y x∈Γ y∈Γ) x≠y with psx-◃-linear→ Γ⊢psz x y x∈Γ y∈Γ
  ... | inl H = H
  ... | inr x=y = ⊥-elim (x≠y x=y)
  snd (ps-◃-linear Γ (ps Γ⊢psz) x .x x∈Γ y∈Γ) (inl x◃x) idp = psx-◃-linear← Γ⊢psz x x∈Γ x◃x
  snd (ps-◃-linear Γ (ps Γ⊢psz) x .x x∈Γ y∈Γ) (inr x◃x) idp = psx-◃-linear← Γ⊢psz x x∈Γ x◃x
