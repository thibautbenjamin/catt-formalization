{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules

{- Decidability of type cheking for the type theory for globular sets -}
module GSeTT.Dec-Type-Checking where

  dec-⊢C : ∀ Γ → dec (Γ ⊢C)
  dec-⊢T : ∀ Γ A → dec (Γ ⊢T A)
  dec-⊢t : ∀ Γ A t → dec (Γ ⊢t t # A)
  dec-⊢S : ∀ Δ Γ γ → dec (Δ ⊢S γ > Γ)

  private
    Γ+⊢→Γ⊢ : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → Γ ⊢C
    Γ+⊢→Γ⊢ (cc Γ⊢ _ idp) = Γ⊢


    Γ+⊢→x=l : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → x == length Γ
    Γ+⊢→x=l (cc _ _ idp) = idp

    Γ+⊢→Γ⊢A : ∀ {Γ x A} → (Γ :: (x , A)) ⊢C → Γ ⊢T A
    Γ+⊢→Γ⊢A (cc _ Γ⊢A _) = Γ⊢A

    Γ⊢t⇒u→Γ⊢A : ∀ {Γ A t u} → Γ ⊢T ⇒ A t u → Γ ⊢T A
    Γ⊢t⇒u→Γ⊢A (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A→Γ⊢A Γ⊢t:A


    Γ⊢t⇒u→Γ⊢t : ∀ {Γ A t u} → Γ ⊢T ⇒ A t u → Γ ⊢t t # A
    Γ⊢t⇒u→Γ⊢t (ar Γ⊢t:A Γ⊢u:A) = Γ⊢t:A

    Γ⊢t⇒u→Γ⊢u : ∀ {Γ A t u} → Γ ⊢T ⇒ A t u → Γ ⊢t u # A
    Γ⊢t⇒u→Γ⊢u (ar Γ⊢t:A Γ⊢u:A) = Γ⊢u:A

    Γ⊢x:A→x∈Γ : ∀ {Γ x A} → Γ ⊢t Var x # A → x # A ∈ Γ
    Γ⊢x:A→x∈Γ (var _ x∈Γ) = x∈Γ

    Δ⊢<>:Γ→Γ=nil : ∀ {Δ Γ} → Δ ⊢S nil > Γ → Γ == nil
    Δ⊢<>:Γ→Γ=nil (es _) = idp

    Δ⊢γ:⊘→γ=nil : ∀ {Δ γ} → Δ ⊢S γ > nil → γ == nil
    Δ⊢γ:⊘→γ=nil (es _) = idp

    Δ⊢γ+:Γ+→x=y : ∀ {Δ Γ x A γ y t} → Δ ⊢S (γ :: (y , t)) > (Γ :: (x , A)) → x == y
    Δ⊢γ+:Γ+→x=y (sc _ _ _ idp) = idp

    Δ⊢γ+:Γ+→Δ⊢t : ∀ {Δ Γ x A γ y t} → Δ ⊢S (γ :: (y , t)) > (Γ :: (x , A)) → Δ ⊢t t # (A [ γ ]Pre-Ty)
    Δ⊢γ+:Γ+→Δ⊢t (sc _ _ Δ⊢t idp) = Δ⊢t

    Δ⊢γ+:Γ+→Δ⊢γ : ∀ {Δ Γ x A γ y t} → Δ ⊢S (γ :: (y , t)) > (Γ :: (x , A)) → Δ ⊢S γ > Γ
    Δ⊢γ+:Γ+→Δ⊢γ (sc Δ⊢γ:Γ _ _ idp) = Δ⊢γ:Γ

  eqdec-Ty : eqdec Pre-Ty
  eqdec-Tm : eqdec Pre-Tm

  eqdec-Ty ∗ ∗ = inl idp
  eqdec-Ty ∗ (⇒ _ _ _) = inr λ{()}
  eqdec-Ty (⇒ _ _ _) ∗ = inr λ{()}
  eqdec-Ty (⇒ A t u) (⇒ B t' u') with eqdec-Ty A B | eqdec-Tm t t' | eqdec-Tm u u'
  ...                                      | inl idp       | inl idp       | inl idp      = inl idp
  ...                                      | inl idp       | inl idp       | inr u≠u'     = inr λ p → u≠u' (snd (=⇒ p))
  ...                                      | inl idp       | inr t≠t'      | _            = inr λ p → t≠t' (snd (fst (=⇒ p)))
  ...                                      | inr A≠B       | _             | _            = inr λ p → A≠B (fst (fst (=⇒ p)))
  eqdec-Tm (Var x) (Var y) with eqdecℕ x y
  ...                               | inl idp = inl idp
  ...                               | inr x≠y = inr λ p → x≠y (=Var p)


  dec-∈ : ∀ Γ x A → dec (x # A ∈ Γ)
  dec-∈ nil x A = inr λ x → x
  dec-∈ (Γ :: (y , B)) x A with (eqdecℕ y x) | (eqdec-Ty B A)
  ...                       | inl idp         | inl idp = inl (inr (idp , idp))
  ...                       | inl idp         | inr B≠A       with dec-∈ Γ x A
  ...                                                         | inl x∈Γ = inl (inl x∈Γ)
  ...                                                         | inr x∉Γ = inr λ {(inl x∈Γ) → x∉Γ x∈Γ ; (inr (_ , A=B)) → B≠A (A=B ^)}
  dec-∈ (Γ :: (y , B)) x A | inr y≠x         | _   with dec-∈ Γ x A
  ...                                               | inl x∈Γ = inl (inl x∈Γ)
  ...                                               | inr x∉Γ = inr λ{ (inl x∈Γ) → x∉Γ x∈Γ ; (inr (x=y , _)) → y≠x (x=y ^)}

  dec-⊢C nil = inl ec
  dec-⊢C (Γ :: (x , A)) with dec-⊢C Γ | eqdecℕ x (length Γ) | dec-⊢T Γ A
  ...                        | inl Γ⊢ | inl idp              | inl Γ⊢A      = inl (cc Γ⊢ Γ⊢A idp)
  ...                        | inl  _ | inl idp              | inr Γ⊬A      = inr λ Γ+⊢ → Γ⊬A (Γ+⊢→Γ⊢A Γ+⊢)
  ...                        | inl Γ⊢ | inr n≠l              | _            = inr λ Γ+⊢ → n≠l (Γ+⊢→x=l Γ+⊢)
  ...                        | inr Γ⊬ | _                    | _            = inr λ Γ+⊢ → Γ⊬ (Γ+⊢→Γ⊢ Γ+⊢)
  dec-⊢T Γ ∗ with dec-⊢C Γ
  ...             | inl Γ⊢ = inl (ob Γ⊢)
  ...             | inr Γ⊬ = inr λ Γ⊢* → Γ⊬ (Γ⊢A→Γ⊢ Γ⊢*)
  dec-⊢T Γ (⇒ A t u) with dec-⊢t Γ A t | dec-⊢t Γ A u
  ...                     | inl Γ⊢t:A    | inl Γ⊢u:A = inl (ar Γ⊢t:A Γ⊢u:A)
  ...                     | inl _        | inr Γ⊬u:A = inr λ Γ⊢t⇒u → Γ⊬u:A (Γ⊢t⇒u→Γ⊢u Γ⊢t⇒u)
  ...                     | inr Γ⊬t:A    | _         = inr λ Γ⊢t⇒u → Γ⊬t:A (Γ⊢t⇒u→Γ⊢t Γ⊢t⇒u)

  dec-⊢t Γ A (Var x) with dec-⊢C Γ       | dec-∈ Γ x A
  ...                     | inl Γ⊢          | inl x∈Γ      = inl (var Γ⊢ x∈Γ)
  ...                     | inl _           | inr x∉Γ      = inr λ Γ⊢x:A → x∉Γ (Γ⊢x:A→x∈Γ Γ⊢x:A)
  ...                     | inr Γ⊬          | _            = inr λ Γ⊢x:A → Γ⊬ (Γ⊢t:A→Γ⊢ Γ⊢x:A)
  dec-⊢S Δ nil nil with dec-⊢C Δ
  ...              | inl Δ⊢ = inl (es Δ⊢)
  ...              | inr Δ⊬ = inr λ Δ⊢<>:⊘ → Δ⊬ (Δ⊢γ:Γ→Δ⊢ Δ⊢<>:⊘)
  dec-⊢S Δ (Γ :: _) nil = inr λ Δ⊢<>:Γ → cons≠nil (Δ⊢<>:Γ→Γ=nil Δ⊢<>:Γ)
  dec-⊢S Δ nil (γ :: a) = inr λ Δ⊢γ:⊘ → cons≠nil (Δ⊢γ:⊘→γ=nil Δ⊢γ:⊘)
  dec-⊢S Δ (Γ :: (x , A)) (γ :: (y , t)) with dec-⊢S Δ Γ γ | dec-⊢C (Γ :: (x , A)) | dec-⊢t Δ (A [ γ ]Pre-Ty) t | eqdecℕ x y
  ...                                    | inl Δ⊢γ:Γ       | inl Γ+⊢               | inl Δ⊢t                    | inl idp    = inl (sc Δ⊢γ:Γ Γ+⊢ Δ⊢t idp)
  ...                                    | inl _           | inl _                 | inl _                      | inr x≠y    = inr λ Δ⊢γ+:Γ+ → x≠y (Δ⊢γ+:Γ+→x=y Δ⊢γ+:Γ+)
  ...                                    | inl _           | inl _                 | inr Δ⊬t                    | _          = inr λ Δ⊢γ+:Γ+ → Δ⊬t (Δ⊢γ+:Γ+→Δ⊢t Δ⊢γ+:Γ+)
  ...                                    | inl _           | inr Γ+⊬               | _                          | _          = inr λ Δ⊢γ+:Γ+ → Γ+⊬ (Δ⊢γ:Γ→Γ⊢ Δ⊢γ+:Γ+)
  ...                                    | inr Δ⊬γ         | _                     | _                          | _          = inr λ Δ⊢γ+:Γ+ → Δ⊬γ (Δ⊢γ+:Γ+→Δ⊢γ Δ⊢γ+:Γ+)
