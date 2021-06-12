{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Syntax
import GSeTT.Rules
open import GSeTT.Typed-Syntax
import Globular-TT.Syntax

module Globular-TT.Rules {l} (index : Set l) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index)) where
  open import Globular-TT.Syntax index

  {- Notational shortcuts : the context corresponding to an index -}
  Ci : index → Pre-Ctx
  Ci i = GPre-Ctx (fst (fst (rule i)))

  Ti : index → Pre-Ty
  Ti i = snd (rule i)

  data _⊢C : Pre-Ctx → Set (lsuc l)
  data _⊢T_ : Pre-Ctx → Pre-Ty → Set (lsuc l)
  data _⊢t_#_ : Pre-Ctx → Pre-Tm → Pre-Ty → Set (lsuc l)
  data _⊢S_>_ : Pre-Ctx → Pre-Sub → Pre-Ctx → Set (lsuc l)

  data _⊢C where
    ec : ⊘ ⊢C
    cc : ∀ {Γ A} → Γ ⊢C → Γ ⊢T A → (Γ ∙ (C-length Γ) # A) ⊢C

  data _⊢T_ where
    ob : ∀ {Γ} → Γ ⊢C → Γ ⊢T ∗
    ar : ∀ {Γ A t u} → Γ ⊢T A → Γ ⊢t t # A → Γ ⊢t u # A → Γ ⊢T ⇒ A t u

  data _⊢t_#_ where
    var : ∀ {Γ x A} → Γ ⊢C → x # A ∈ Γ → Γ ⊢t (Var x) # A
    tm : ∀ {Δ γ} → (i : index) → Ci i ⊢T Ti i → Δ ⊢S γ > Ci i → Δ ⊢t Tm-constructor i γ # (Ti i [ γ ]Pre-Ty)

  data _⊢S_>_ where
    es : ∀ {Δ} → Δ ⊢C → Δ ⊢S <> > ⊘
    sc : ∀ {Δ Γ γ x A t} → Δ ⊢S γ > Γ → (Γ ∙ x # A) ⊢C → (Δ ⊢t t # (A [ γ ]Pre-Ty)) → Δ ⊢S < γ , x ↦ t > > (Γ ∙ x # A)


  {- Derivability is preserved by the translation from GSeTT to our TT -}
  x∈GCtx : ∀ {x A Γ} → x GSeTT.Syntax.# A ∈ Γ → x # GPre-Ty A ∈ GPre-Ctx Γ
  x∈GCtx {Γ = Γ :: a} (inl x∈Γ) = inl (x∈GCtx x∈Γ)
  x∈GCtx {Γ = Γ :: (x,A)} (inr (idp , idp)) = inr (idp , idp)

  G-length : ∀ Γ → length Γ == C-length (GPre-Ctx Γ)
  G-length nil = idp
  G-length (Γ :: _) = S= (G-length Γ)


  GCtx : ∀ (Γ : GSeTT.Syntax.Pre-Ctx) → Γ GSeTT.Rules.⊢C → (GPre-Ctx Γ) ⊢C
  GTy : ∀ (Γ : GSeTT.Syntax.Pre-Ctx) (A : GSeTT.Syntax.Pre-Ty) → Γ GSeTT.Rules.⊢T A → (GPre-Ctx Γ) ⊢T (GPre-Ty A)
  GTm : ∀ (Γ : GSeTT.Syntax.Pre-Ctx) (A : GSeTT.Syntax.Pre-Ty) (t : GSeTT.Syntax.Pre-Tm) → Γ GSeTT.Rules.⊢t t # A  → (GPre-Ctx Γ) ⊢t (GPre-Tm t) # (GPre-Ty A)

  GCtx .nil GSeTT.Rules.ec = ec
  GCtx (Γ :: (.(length Γ) , A)) (GSeTT.Rules.cc Γ⊢ Γ⊢A idp) = coe (ap (λ n → (GPre-Ctx (Γ :: (n , A)) ⊢C)) (G-length Γ) ^) (cc (GCtx Γ Γ⊢) (GTy Γ A Γ⊢A))
  GTy Γ .GSeTT.Syntax.∗ (GSeTT.Rules.ob Γ⊢) = ob (GCtx Γ Γ⊢)
  GTy Γ (GSeTT.Syntax.⇒ A t u) (GSeTT.Rules.ar Γ⊢t:A Γ⊢u:A) = ar (GTy Γ A (GSeTT.Rules.Γ⊢t:A→Γ⊢A Γ⊢t:A)) (GTm Γ A t Γ⊢t:A) (GTm Γ A u Γ⊢u:A)
  GTm Γ A (GSeTT.Syntax.Var x) (GSeTT.Rules.var Γ⊢ x∈Γ) = var (GCtx Γ Γ⊢) (x∈GCtx x∈Γ)


  {- Properties of the type theory -}
  {- weakening admissibility -}
  wkT : ∀ {Γ A y B} → Γ ⊢T A → (Γ ∙ y # B) ⊢C → (Γ ∙ y # B) ⊢T A
  wkt : ∀ {Γ A t y B} → Γ ⊢t t # A → (Γ ∙ y # B) ⊢C → (Γ ∙ y # B) ⊢t t # A
  wkS : ∀ {Δ Γ γ y B} → Δ ⊢S γ > Γ → (Δ ∙ y # B) ⊢C → (Δ ∙ y # B) ⊢S γ > Γ

  wkT (ob _) Γ,y:B⊢ = ob Γ,y:B⊢
  wkT (ar Γ⊢A Γ⊢t:A Γ⊢u:A) Γ,y:B⊢ = ar (wkT Γ⊢A Γ,y:B⊢) (wkt Γ⊢t:A Γ,y:B⊢) (wkt Γ⊢u:A Γ,y:B⊢)
  wkt (var Γ⊢C x∈Γ) Γ,y:B⊢ = var Γ,y:B⊢ (inl x∈Γ)
  wkt (tm i Ci⊢Ti Γ⊢γ:Δ) Γ,y:B⊢ = tm i Ci⊢Ti (wkS Γ⊢γ:Δ Γ,y:B⊢)
  wkS (es _) Δ,y:B⊢ = es Δ,y:B⊢
  wkS (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) Δ,y:B⊢ = sc (wkS Δ⊢γ:Γ Δ,y:B⊢) Γ,x:A⊢ (wkt Δ⊢t:A[γ] Δ,y:B⊢)


  {- Consistency : all objects appearing in derivable judgments are derivable -}
  Γ⊢A→Γ⊢ : ∀ {Γ A} → Γ ⊢T A → Γ ⊢C
  Γ⊢t:A→Γ⊢ : ∀ {Γ A t} → Γ ⊢t t # A → Γ ⊢C
  Δ⊢γ:Γ→Δ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Δ ⊢C

  Γ⊢A→Γ⊢ (ob Γ⊢) = Γ⊢
  Γ⊢A→Γ⊢ (ar Γ⊢A Γ⊢t:A Γ⊢u:A) = Γ⊢t:A→Γ⊢ Γ⊢t:A
  Γ⊢t:A→Γ⊢ (var Γ⊢ _) = Γ⊢
  Γ⊢t:A→Γ⊢ (tm i _ Γ⊢γ:Δ) = Δ⊢γ:Γ→Δ⊢ Γ⊢γ:Δ
  Δ⊢γ:Γ→Δ⊢ (es Δ⊢) = Δ⊢
  Δ⊢γ:Γ→Δ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Δ⊢γ:Γ→Δ⊢ Δ⊢γ:Γ

  Δ⊢γ:Γ→Γ⊢ : ∀ {Δ Γ γ} → Δ ⊢S γ > Γ → Γ ⊢C
  Δ⊢γ:Γ→Γ⊢ (es Δ⊢) = ec
  Δ⊢γ:Γ→Γ⊢ (sc Δ⊢γ:Γ Γ,x:A⊢ Δ⊢t:A[γ]) = Γ,x:A⊢

  Γ,x:A⊢→Γ,x:A⊢A : ∀ {Γ x A} → (Γ ∙ x # A) ⊢C → (Γ ∙ x # A) ⊢T A
  Γ,x:A⊢→Γ,x:A⊢A Γ,x:A⊢@(cc Γ⊢ Γ⊢A) = wkT Γ⊢A Γ,x:A⊢

  Γ,x:A⊢→Γ,x:A⊢x:A : ∀ {Γ x A} → (Γ ∙ x # A) ⊢C → (Γ ∙ x # A) ⊢t (Var x) # A
  Γ,x:A⊢→Γ,x:A⊢x:A Γ,x:A⊢ = var Γ,x:A⊢ (inr (idp , idp))

  -- The proposition Γ⊢t:A→Γ⊢A is slightly harder and is moved in CwF-Struture since it depends on lemmas there

  -- Type epressing that the rules are well-founded (useful to show that judgments are decidable)
  well-founded : Set (lsuc l)
  well-founded = ∀ (i : index) → Ci i ⊢T Ti i → dimC (Ci i) ≤ dim (Ti i)
