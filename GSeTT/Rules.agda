{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax

{- Typing Rules and basic syntactic properties for the type theory for globular sets -}
module GSeTT.Rules where
  {- Well-formedness statements ≡ inference rules -}
  data _⊢C : Pre-Ctx → Set
  data _⊢T_ : Pre-Ctx → Pre-Ty → Set
  data _⊢t_#_ : Pre-Ctx → Pre-Tm → Pre-Ty → Set
  data _⊢S_>_ : Pre-Ctx → Pre-Sub → Pre-Ctx → Set

  data _⊢C where
    ec : nil ⊢C
    cc : ∀ {Γ A} → Γ ⊢C → Γ ⊢T A → (Γ :: ((length Γ) , A)) ⊢C

  data _⊢T_ where
    ob : ∀ {Γ} → Γ ⊢C → Γ ⊢T ∗
    ar : ∀ {Γ A t u} → Γ ⊢t t # A → Γ ⊢t u # A → Γ ⊢T ⇒ A t u

  data _⊢t_#_ where
    var : ∀ {Γ x A} → Γ ⊢C → x # A ∈ Γ → Γ ⊢t (Var x) # A

  data _⊢S_>_ where
    es : ∀ {Δ} → Δ ⊢C → Δ ⊢S nil > nil
    sc : ∀ {Δ Γ γ x A t} → Δ ⊢S γ > Γ → (Γ :: (x , A)) ⊢C → (Δ ⊢t t # (A [ γ ]Pre-Ty)) → Δ ⊢S (γ :: (x , t)) > (Γ :: (x , A))

  {- Weakening admissibility -}

  wkT : ∀ {Γ A y B} → Γ ⊢T A → (Γ :: (y , B)) ⊢C → (Γ :: (y , B)) ⊢T A
  wkt : ∀ {Γ A t y B} → Γ ⊢t t # A → (Γ :: (y , B)) ⊢C → (Γ :: (y , B)) ⊢t t # A

  wkT (ob _) Γ,y:B⊢ = ob Γ,y:B⊢
  wkT (ar Γ⊢t:A Γ⊢u:A) Γ,y:B⊢ = ar (wkt Γ⊢t:A Γ,y:B⊢) (wkt Γ⊢u:A Γ,y:B⊢)
  wkt (var Γ⊢C x∈Γ) Γ,y:B⊢ = var Γ,y:B⊢ (inl x∈Γ)

  wkS : ∀ {Δ Γ γ y B} → Δ ⊢S γ > Γ → (Δ :: (y , B)) ⊢C → (Δ :: (y , B)) ⊢S γ > Γ
  wkS (es _) Δ,y:B⊢ = es Δ,y:B⊢
  wkS (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) Δ,y:B⊢ = sc (wkS Δ⊢γ:Γ Δ,y:B⊢) Γ,x:A⊢ (wkt Δ⊢t:A[γ] Δ,y:B⊢)


  {- Consistency : all objects appearing in derivable judgments are derivable -}
  Γ⊢A→Γ⊢ : ∀ {Γ A} → Γ ⊢T A → Γ ⊢C
  Γ⊢t:A→Γ⊢ : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢C

  Γ⊢A→Γ⊢ (ob Γ⊢) = Γ⊢
  Γ⊢A→Γ⊢ (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A→Γ⊢ Γ⊢t:A
  Γ⊢t:A→Γ⊢ (var Γ⊢ _) = Γ⊢

  Δ⊢γ:Γ→Γ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Γ ⊢C
  Δ⊢γ:Γ→Γ⊢ (es Δ⊢) = ec
  Δ⊢γ:Γ→Γ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Γ,x:A⊢

  Δ⊢γ:Γ→Δ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Δ ⊢C
  Δ⊢γ:Γ→Δ⊢ (es Δ⊢) = Δ⊢
  Δ⊢γ:Γ→Δ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ

  Γ,x:A⊢→Γ,x:A⊢A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢T A
  Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = wkT Γ⊢A Γ,x:A⊢

  Γ,x:A⊢→Γ,x:A⊢x:A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → (Γ :: (x , A)) ⊢t (Var x) # A
  Γ,x:A⊢→Γ,x:A⊢x:A Γ,x:A⊢ = var Γ,x:A⊢ (inr (idp , idp))

  Γ⊢t:A→Γ⊢A : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢T A
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc Γ⊢ Γ⊢A) (inl y∈Γ)) = wkT (Γ⊢t:A→Γ⊢A (var Γ⊢ y∈Γ)) Γ,x:A⊢
  Γ⊢t:A→Γ⊢A (var Γ,x:A⊢@(cc _ _) (inr (idp , idp))) = Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢

  {- Cut-admissibility -}
  -- notational shortcut : if A = B a term of type A is also of type B
  trT : ∀ {Γ A B t} → A == B → Γ ⊢t t # A → Γ ⊢t t # B
  trT idp Γ⊢t:A = Γ⊢t:A

  n∉Γ : ∀ {Γ A n} → Γ ⊢C → (length Γ ≤ n) → ¬ (n # A ∈ Γ)
  n∉Γ (cc Γ⊢ _) l+1≤n (inl n∈Γ) = n∉Γ Γ⊢ (Sn≤m→n≤m l+1≤n) n∈Γ
  n∉Γ (cc Γ⊢ _) Sn≤n (inr (idp , idp)) = Sn≰n _ Sn≤n

  lΓ∉Γ : ∀ {Γ A} → Γ ⊢C → ¬ ((length Γ) # A ∈ Γ)
  lΓ∉Γ Γ⊢ = n∉Γ Γ⊢ (n≤n _)

  {- action on weakened types and terms -} 
  wk[]T : ∀ {Γ Δ γ x u A B} → Γ ⊢T A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (A [ (γ :: (x , u)) ]Pre-Ty) == (A [ γ ]Pre-Ty)
  wk[]t : ∀ {Γ Δ γ x u A t B} → Γ ⊢t t # A → Δ ⊢S (γ :: (x , u)) > (Γ :: (x , B)) → (t [ (γ :: (x , u)) ]Pre-Tm) == (t [ γ ]Pre-Tm)

  wk[]T (ob Γ⊢) _ = idp
  wk[]T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ+:Γ+ = ⇒= (wk[]T (Γ⊢t:A→Γ⊢A Γ⊢t:A) Δ⊢γ+:Γ+)  (wk[]t Γ⊢t:A Δ⊢γ+:Γ+) (wk[]t Γ⊢u:A Δ⊢γ+:Γ+)
  wk[]t {x = x} (var {x = y} Γ⊢ y∈Γ) Δ⊢γ+:Γ+             with (eqdecℕ y x)
  ...                                                    | inr _ = idp
  wk[]t (var Γ⊢ l∈Γ) (sc Δ⊢γ:Γ (cc _ _) _) | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ l∈Γ)


  {- cut-admissibility : action of substitutions preserves derivability -}
  []T : ∀ {Γ A Δ γ} → Γ ⊢T A → Δ ⊢S γ > Γ → Δ ⊢T (A [ γ ]Pre-Ty)
  []t : ∀ {Γ A t Δ γ} → Γ ⊢t t # A → Δ ⊢S γ > Γ → Δ ⊢t (t [ γ ]Pre-Tm) # (A [ γ ]Pre-Ty)

  []T (ob Γ⊢) Δ⊢γ:Γ = ob (Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ)
  []T (ar Γ⊢t:A Γ⊢u:A) Δ⊢γ:Γ = ar ([]t Γ⊢t:A Δ⊢γ:Γ) ([]t Γ⊢u:A Δ⊢γ:Γ)
  []t {Γ = (Γ :: _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ _) (inl x∈Γ)) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ _ _) with (eqdecℕ x (length Γ))
  ...                                                                                     | inl idp = ⊥-elim (lΓ∉Γ Γ⊢ x∈Γ)
  ...                                                                                     | inr _ = trT (wk[]T (Γ⊢t:A→Γ⊢A (var Γ⊢ x∈Γ)) Δ⊢γ+:Γ+ ^) ([]t (var Γ⊢ x∈Γ) Δ⊢γ:Γ)
  []t {Γ = (Γ :: _)} {t = Var x} (var Γ+⊢@(cc Γ⊢ Γ⊢A) (inr (idp , idp))) Δ⊢γ+:Γ+@(sc Δ⊢γ:Γ x₁ Δ⊢t:A[γ]) with (eqdecℕ x (length Γ))
  ...                                                                                     | inl idp = trT (wk[]T Γ⊢A Δ⊢γ+:Γ+ ^) Δ⊢t:A[γ]
  ...                                                                                     | inr x≠x = ⊥-elim (x≠x idp)
