{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Rules
import GSeTT.Typed-Syntax
import Globular-TT.Syntax
import Globular-TT.Rules

{- Decidability of type cheking for the type theory for globular sets -}
module Globular-TT.Dec-Type-Checking {l} (index : Set l) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index))
                                                   (assumption : Globular-TT.Rules.well-founded index rule)
                                                   (eqdec-index : eqdec index) where
  open import Globular-TT.Syntax index
  open import Globular-TT.Rules index rule
  open import Globular-TT.CwF-Structure index rule

  eqdec-Ty : eqdec Pre-Ty
  eqdec-Tm : eqdec Pre-Tm
  eqdec-Sub : eqdec Pre-Sub

  eqdec-Ty ∗ ∗ = inl idp
  eqdec-Ty ∗ (⇒ _ _ _) = inr λ{()}
  eqdec-Ty (⇒ _ _ _ ) ∗ = inr λ{()}
  eqdec-Ty (⇒ A t u) (⇒ B t' u') with eqdec-Ty A B | eqdec-Tm t t' | eqdec-Tm u u'
  ...                            | inl idp | inl idp | inl idp = inl idp
  ...                            | inr A≠B | _ | _ = inr λ{idp → A≠B idp}
  ...                            | inl idp | inr t≠t' | _ = inr λ{idp → t≠t' idp}
  ...                            | inl idp | inl idp | inr u≠u' = inr λ{idp → u≠u' idp}
  eqdec-Tm (Var x) (Var y) with eqdecℕ x y
  ...                      | inl idp = inl idp
  ...                      | inr x≠y = inr λ {idp → x≠y idp}
  eqdec-Tm (Var _) (Tm-constructor _ _) = inr λ{()}
  eqdec-Tm (Tm-constructor _ _) (Var _) = inr λ{()}
  eqdec-Tm (Tm-constructor i γ) (Tm-constructor i' γ') with eqdec-index i i' | eqdec-Sub γ γ'
  ...                                                   | inl idp | inl idp = inl idp
  ...                                                   | inr i≠i' | _ = inr λ{idp → i≠i' idp}
  ...                                                   | inl idp | inr γ≠γ' = inr λ{idp → γ≠γ' idp}
  eqdec-Sub <> <> = inl idp
  eqdec-Sub < _ , _ ↦ _ > <> = inr λ{()}
  eqdec-Sub <> < _ , _ ↦ _ > = inr λ{()}
  eqdec-Sub < γ , x ↦ t > < γ' , y ↦ t' > with eqdec-Sub γ γ' | eqdecℕ x y | eqdec-Tm t t'
  ...                                      | inl idp | inl idp | inl idp = inl idp
  ...                                      | inr γ≠γ' | _ | _ = inr λ{idp → γ≠γ' idp}
  ...                                      | inl idp | inr x≠y | _ = inr λ{idp → x≠y idp}
  ...                                      | inl idp | inl idp | inr t≠t' = inr λ{idp → t≠t' idp}



  dec-∈ : ∀ (n : ℕ) (A : Pre-Ty) (Γ : Pre-Ctx) → dec (n # A ∈ Γ)
  dec-∈ n A ⊘ = inr λ{()}
  dec-∈ n A (Γ ∙ x # B) with dec-∈ n A Γ
  ...                    | inl n∈Γ = inl (inl n∈Γ)
  ...                    | inr n∉Γ with eqdecℕ n x | eqdec-Ty A B
  ...                              | inl idp | inl idp = inl (inr (idp , idp))
  ...                              | inr n≠x | _ = inr λ{(inl n∈Γ) → n∉Γ n∈Γ; (inr (idp , idp)) → n≠x idp}
  ...                              | inl idp | inr A≠B_ = inr λ{(inl n∈Γ) → n∉Γ n∈Γ; (inr (idp , idp)) → A≠B idp}

  {- Decidability in the fragment of the theory with only globular contexts -}
  -- termination is really tricky, and involves reasonning both on depth and dimension at the same time !
  dec-G⊢T : ∀ (Γ : GSeTT.Typed-Syntax.Ctx) n A → dim A ≤ n →  dec (GPre-Ctx (fst Γ) ⊢T A)
  dec-G⊢t : ∀ (Γ : GSeTT.Typed-Syntax.Ctx) n d A t → dim A ≤ n → depth t ≤ d →  dec (GPre-Ctx (fst Γ) ⊢t t # A)
  dec-G⊢S : ∀ (Δ Γ : GSeTT.Typed-Syntax.Ctx) n d γ → dimC (GPre-Ctx (fst Γ)) ≤ n → depthS γ ≤ d → dec (GPre-Ctx (fst Δ) ⊢S γ > GPre-Ctx (fst Γ))

  dec-G⊢T Γ _ ∗ _ = inl (ob (GCtx _ (snd Γ)))
  dec-G⊢T Γ (S n) (⇒ A t u) (S≤ i)  with dec-G⊢T Γ n A i | dec-G⊢t Γ n _ A t i (n≤n _) | dec-G⊢t Γ n _ A u i (n≤n _)
  ...                         | inl Γ⊢A | inl Γ⊢t:A | inl Γ⊢u:A = inl (ar Γ⊢A Γ⊢t:A Γ⊢u:A)
  ...                         | inr Γ⊬A | _ | _ = inr λ{(ar Γ⊢A _ _) → Γ⊬A Γ⊢A}
  ...                         | inl _ | inr Γ⊬t:A  | _ = inr λ{(ar _ Γ⊢t:A _) → Γ⊬t:A Γ⊢t:A}
  ...                         | inl _ | inl _  | inr Γ⊬u:A = inr λ{(ar _ _ Γ⊢u:A) → Γ⊬u:A Γ⊢u:A}

  dec-G⊢t Γ n _ A (Var x) _ (0≤ _) with dec-∈ x A (GPre-Ctx (fst Γ))
  ...                              | inl x∈Γ = inl (var (GCtx _ (snd Γ)) x∈Γ)
  ...                              | inr x∉Γ = inr λ {(var _ x∈Γ) → x∉Γ x∈Γ}
  dec-G⊢t Γ n (S d) A (Tm-constructor i γ) dimA≤n (S≤ dγ≤d) with eqdec-Ty A (Ti i [ γ ]Pre-Ty )
  ...                                         | inr A≠Ti = inr λ{(tm _ _ _) → A≠Ti idp}
  ...                                         | inl idp
                                                    with dec-G⊢T (fst (rule i)) n (Ti i) (=-≤ (dim[] _ _ ^) dimA≤n)
  ...                                                 | inr Ci⊬Ti = inr λ{(tm _ Ci⊢Ti _) → Ci⊬Ti Ci⊢Ti}
  ...                                                 | inl Ci⊢Ti with dec-G⊢S Γ (fst (rule i)) n d γ
                                                                               (≤T (≤-= (assumption i Ci⊢Ti) (dim[] _ _ ^)) dimA≤n)    -- dim Ci ≤ dim A
                                                                               dγ≤d                                                    -- depth γ ≤ d
  ...                                                             | inr Γ⊬γ = inr λ{(tm _ _ Γ⊢γ) → Γ⊬γ Γ⊢γ}
  ...                                                             | inl Γ⊢γ = inl (tm i Ci⊢Ti Γ⊢γ)


  dec-G⊢S Δ (nil , _) _ _ <> (0≤ _) _ = inl (es (GCtx _ (snd Δ)))
  dec-G⊢S Δ ((Γ :: _) , _) _ _ <> _ _ = inr λ {()}
  dec-G⊢S Δ (nil , _) _ _ < γ , x ↦ t > _ _ = inr λ {()}
  dec-G⊢S Δ ((Γ :: (y , A)) , Γ+⊢@(GSeTT.Rules.cc Γ⊢ Γ⊢A)) n d < γ , x ↦ t > dimΓ+≤n dγ+≤d with dec-G⊢S Δ (Γ , Γ⊢) n d γ
                                                                                                      (≤T (n≤max (dimC (GPre-Ctx Γ)) (dim (GPre-Ty A))) dimΓ+≤n) -- dim Γ ≤ n
                                                                                                      (≤T (n≤max (depthS γ) (depth t)) dγ+≤d)                    -- depth γ ≤ d
                                                                                          | dec-G⊢t Δ n d ((GPre-Ty A) [ γ ]Pre-Ty) t
                                                                                                      ((≤T (=-≤ (dim[] _ _) (m≤max (dimC (GPre-Ctx Γ)) (dim (GPre-Ty A)))) dimΓ+≤n)) -- dim A[γ] ≤ n
                                                                                                      (≤T (m≤max (depthS γ) (depth t)) dγ+≤d)                                        -- depth t ≤ d
                                                                                          | eqdecℕ y x
  ...                                                    | inl Δ⊢γ:Γ | inl Δ⊢t | inl idp = inl (sc Δ⊢γ:Γ (GCtx _ Γ+⊢) Δ⊢t)
  ...                                                    | inr Δ⊬γ:Γ | _ | _  = inr λ {(sc Δ⊢γ:Γ _ _) → Δ⊬γ:Γ Δ⊢γ:Γ}
  ...                                                    | inl _ | inr Δ⊬t | _ = inr λ {(sc _ _ Δ⊢t) → Δ⊬t Δ⊢t}
  ...                                                    | inl _ | inl _ | inr n≠x = inr λ {(sc _ _ _) → n≠x idp}


  {- Decidability of judgments for contexts, types, terms and substitution towards a glaobular context -}
  dec-⊢C : ∀ Γ → dec (Γ ⊢C)
  dec-⊢T : ∀ Γ A →  dec (Γ ⊢T A)
  dec-⊢t : ∀ Γ A t → dec (Γ ⊢t t # A)
  dec-⊢S:G : ∀ Δ (Γ : GSeTT.Typed-Syntax.Ctx) γ → dec (Δ ⊢S γ > GPre-Ctx (fst Γ))

  dec-⊢T Γ ∗ with dec-⊢C Γ
  ...        | inl Γ⊢ = inl (ob Γ⊢)
  ...        | inr Γ⊬ = inr λ {(ob Γ⊢) → Γ⊬ Γ⊢}

  dec-⊢T Γ (⇒ A t u) with dec-⊢T Γ A | dec-⊢t Γ A t | dec-⊢t Γ A u
  ...                 | inl Γ⊢A | inl Γ⊢t:A | inl Γ⊢u:A = inl (ar Γ⊢A Γ⊢t:A Γ⊢u:A)
  ...                 | inr Γ⊬A | _ | _ = inr λ {(ar Γ⊢A _ _) → Γ⊬A Γ⊢A}
  ...                 | inl _ | inr Γ⊬t:A | _ = inr λ {(ar _ Γ⊢t:A _) → Γ⊬t:A Γ⊢t:A}
  ...                 | inl _ | inl _ | inr Γ⊬u:A = inr λ {(ar _ _ Γ⊢u:A) → Γ⊬u:A Γ⊢u:A}

  dec-⊢t Γ A (Var x) with dec-⊢C Γ | dec-∈ x A Γ
  ...                | inl Γ⊢ | inl x∈Γ = inl (var Γ⊢ x∈Γ)
  ...                | inr Γ⊬ | _ = inr λ {(var Γ⊢ _) → Γ⊬ Γ⊢}
  ...                | inl _ | inr x∉Γ = inr λ {(var _ x∈Γ) → x∉Γ x∈Γ}
  dec-⊢t Γ A (Tm-constructor i γ) with eqdec-Ty A (Ti i [ γ ]Pre-Ty)
  ...                                   | inr A≠Ti = inr λ{(tm _ _ _) → A≠Ti idp}
  ...                                   | inl idp
                                              with dec-G⊢T (fst (rule i)) _ (Ti i) (n≤n _) | dec-⊢S:G Γ (fst (rule i)) γ
  ...                                              | inl Ci⊢Ti | inl Γ⊢γ = inl (tm i Ci⊢Ti Γ⊢γ)
  ...                                              | inr Ci⊬Ti | _ = inr λ{(tm _ Ci⊢Ti _) → Ci⊬Ti Ci⊢Ti}
  ...                                              | inl _ | inr Γ⊬γ = inr λ{(tm _ _ Γ⊢γ) → Γ⊬γ Γ⊢γ}


  dec-⊢C ⊘ = inl ec
  dec-⊢C (Γ ∙ n # A) with dec-⊢C Γ | dec-⊢T Γ A | eqdecℕ n (C-length Γ)
  ...                 | inl Γ⊢ | inl Γ⊢A | inl idp = inl (cc Γ⊢ Γ⊢A)
  ...                 | inr Γ⊬ | _ | _ = inr λ {(cc Γ⊢ _) → Γ⊬ Γ⊢}
  ...                 | inl _ | inr Γ⊬A | _ = inr λ {(cc _ Γ⊢A) → Γ⊬A Γ⊢A}
  ...                 | inl _ | inl _ | inr n≠l = inr λ {(cc _ _) → n≠l idp}


  dec-⊢S:G Δ (nil , _) <> with (dec-⊢C Δ)
  ...             | inl Δ⊢ = inl (es Δ⊢)
  ...             | inr Δ⊬ = inr λ{(es Δ⊢) → Δ⊬ Δ⊢}
  dec-⊢S:G Δ (nil , _) < γ , x ↦ x₁ > = inr λ{()}
  dec-⊢S:G Δ ((Γ :: _) , _) <> = inr λ{()}
  dec-⊢S:G Δ ((Γ :: (v , A)) , Γ+⊢@(GSeTT.Rules.cc Γ⊢ Γ⊢A)) < γ , x ↦ t > with dec-⊢S:G Δ (Γ , Γ⊢) γ | dec-⊢t Δ ((GPre-Ty A) [ γ ]Pre-Ty) t | eqdecℕ x (length Γ)
  ...                                                                | inl Δ⊢γ | inl Δ⊢t | inl idp = inl (sc Δ⊢γ (GCtx _ Γ+⊢) Δ⊢t)
  ...                                                                | inr Δ⊬γ | _ | _ = inr λ{(sc Δ⊢γ _ _) → Δ⊬γ Δ⊢γ}
  ...                                                                | inl _ | inr Δ⊬t | _ = inr λ{(sc _ _ Δ⊢t) → Δ⊬t Δ⊢t}
  ...                                                                | inl _ | inl _ | inr x≠x = inr λ{(sc _ _ _) → x≠x idp}


  {- Decidability of substitution -}
  dec-⊢S : ∀ Δ Γ γ → dec (Δ ⊢S γ > Γ)
  dec-⊢S Δ ⊘ <> with (dec-⊢C Δ)
  ...             | inl Δ⊢ = inl (es Δ⊢)
  ...             | inr Δ⊬ = inr λ{(es Δ⊢) → Δ⊬ Δ⊢}
  dec-⊢S Δ ⊘ < γ , x ↦ x₁ > = inr λ{()}
  dec-⊢S Δ (Γ ∙ _ # _) <> = inr λ{()}
  dec-⊢S Δ (Γ ∙ v # A) < γ , x ↦ t > with dec-⊢S Δ Γ γ | dec-⊢C (Γ ∙ v # A) | dec-⊢t Δ (A [ γ ]Pre-Ty) t | eqdecℕ x v
  ...                                                                | inl Δ⊢γ | inl Γ+⊢ | inl Δ⊢t | inl idp  = inl (sc Δ⊢γ Γ+⊢ Δ⊢t)
  ...                                                                | inr Δ⊬γ | _ | _ | _  = inr λ{(sc Δ⊢γ _ _) → Δ⊬γ Δ⊢γ}
  ...                                                                | inl _ | inr Γ+⊬ | _ | _  = inr λ{(sc _ Γ⊢ _) → Γ+⊬ Γ⊢}
  ...                                                                | inl _ | inl _ | inr Δ⊬t | _  = inr λ{(sc _ _ Δ⊢t) → Δ⊬t Δ⊢t}
  ...                                                                | inl _ | inl _ | inl _ | inr x≠x  = inr λ{(sc _ _ _) → x≠x idp}
