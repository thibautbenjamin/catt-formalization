{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax

{- Disk and Sphere contexts - properties -}
module Globular-TT.Disks {l} (index : Set l) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index)) (eqdec-index : eqdec index) where
  open import Globular-TT.Syntax index
  open import Globular-TT.Rules index rule
  open import Globular-TT.CwF-Structure index rule
  open import Globular-TT.Uniqueness-Derivations index rule eqdec-index
  open import Globular-TT.Typed-Syntax index rule eqdec-index



  {- Definition of "universal source and target variables" -}
  n-src : ℕ → ℕ
  n-tgt : ℕ → ℕ
  n⇒ : ℕ → Pre-Ty

  n-src O = O
  n-src (S n) = S (n-tgt n)
  n-tgt n = S (n-src n)

  n⇒ O = ∗
  n⇒ (S n) = ⇒ (n⇒ n) (Var (n-src n)) (Var (n-tgt  n))

  dim⇒ : ∀ (n : ℕ) → dim (n⇒ n) == n
  dim⇒ O = idp
  dim⇒ (S n) = S= (dim⇒ n)

  {- Syntactic definition of disks and spheres -}
  Pre-𝕊 : ℕ → Pre-Ctx
  Pre-𝔻 : ℕ → Pre-Ctx

  Pre-𝕊 O = ⊘
  Pre-𝕊 (S n) = (Pre-𝔻 n) ∙ C-length (Pre-𝔻 n) # n⇒ n
  Pre-𝔻 n = (Pre-𝕊 n) ∙ C-length (Pre-𝕊 n) # n⇒ n

  𝕊-length : ∀ n → C-length (Pre-𝕊 n) == n-src n
  𝕊-length O = idp
  𝕊-length (S n) = S= (S= (𝕊-length n))

  {- Disk and Sphere context are valid -}
  𝕊⊢ : ∀ n → Pre-𝕊 n ⊢C
  𝔻⊢ : ∀ n → Pre-𝔻 n ⊢C
  𝕊⊢⇒ : ∀ n → Pre-𝕊 n ⊢T n⇒ n

  𝕊⊢ O = ec
  𝕊⊢ (S n) = cc (𝔻⊢ n) (wkT (𝕊⊢⇒ n) (𝔻⊢ n)) idp
  𝔻⊢ n = cc (𝕊⊢ n) (𝕊⊢⇒ n) idp

  𝕊⊢⇒ O = ob ec
  𝕊⊢⇒ (S n) = ar (wkT (wkT (𝕊⊢⇒ n) (𝔻⊢ n)) (𝕊⊢ (S n))) (wkt (var (𝔻⊢ n) (inr (((𝕊-length n) ^) , idp))) (𝕊⊢ (S n))) (var (𝕊⊢ (S n)) (inr ((S= (𝕊-length n) ^) , idp)))

  𝕊 : ℕ → Ctx
  𝕊 n = Pre-𝕊 n , 𝕊⊢ n

  𝔻 : ℕ → Ctx
  𝔻 n = Pre-𝔻 n , 𝔻⊢ n


  Ty-n : ∀ {Γ} → Σ ℕ (λ n →  Sub Γ (𝕊 n)) → Ty Γ
  Ty-n {Γ} (n , (γ , Γ⊢γ:Sn) ) = ((n⇒ n)[ γ ]Pre-Ty) , ([]T (𝕊⊢⇒ n) Γ⊢γ:Sn)

  private
    Pre-χ : Pre-Ty → Pre-Sub

    Pre-χ ∗ = <>
    Pre-χ (⇒ A t u) = < < Pre-χ A , n-src (dim A) ↦ t > , n-tgt (dim A) ↦ u >

    χ_⊢ : ∀ {Γ A} → (Γ⊢A : Γ ⊢T A) → Γ ⊢S (Pre-χ A) > Pre-𝕊 (dim A)
    ⇒[χ_] : ∀ {Γ A} → (Γ⊢A : Γ ⊢T A) → A == ((n⇒  (dim A))[ Pre-χ A ]Pre-Ty)

    χ ob Γ⊢ ⊢ = es Γ⊢
    χ_⊢ {Γ} {⇒ A t u} (ar Γ⊢A Γ⊢t:A Γ⊢u:A) =
      let Γ⊢χt = transport {B = λ n → Γ ⊢S < Pre-χ A , n ↦ t > > Pre-𝔻 (dim A) } (𝕊-length (dim A)) (sc χ Γ⊢A ⊢ (𝔻⊢ (dim A)) (trT (⇒[χ Γ⊢A ]) Γ⊢t:A) idp) in
      sc
        Γ⊢χt
        (𝕊⊢ (S (dim A)))
        (trT (⇒[χ Γ⊢A ] >> (wk[]T (𝕊⊢⇒ (dim A)) (transport {B = λ n → Γ ⊢S < Pre-χ A , n-src (dim A) ↦ t > > (Pre-𝕊 (dim A) Globular-TT.Syntax.∙ n # n⇒ (dim A)) } (𝕊-length (dim A)) Γ⊢χt) ^)) Γ⊢u:A)
        (ap S (𝕊-length (dim A)))

    ⇒[χ_] {Γ} {.∗} (ob _) = idp
    ⇒[χ_] {Γ} {(⇒ A t u)} (ar Γ⊢A Γ⊢t:A Γ⊢u:A) with eqdecℕ (n-src (dim A)) (n-tgt (dim A)) | eqdecℕ (n-src (dim A)) (n-src (dim A)) | eqdecℕ (S (n-src (dim A))) (S (n-src (dim A)))
    ...                                     | inl contra | _ | _ = ⊥-elim (n≠Sn _ contra)
    ...                                     | inr _ | inr n≠n | _ = ⊥-elim (n≠n idp)
    ...                                     | inr _ | inl _ | inr n≠n = ⊥-elim (n≠n idp)
    ...                                     | inr _ | inl _ | inl _ =
      let Γ⊢χt = (sc χ Γ⊢A ⊢ (𝔻⊢(dim A)) (trT ⇒[χ Γ⊢A ] Γ⊢t:A) idp) in
      let A=⇒[γt] = ⇒[χ Γ⊢A ] >> (wk[]T (𝕊⊢⇒ (dim A)) Γ⊢χt ^) in
      ⇒= (A=⇒[γt] >> (wk[]T (wkT (𝕊⊢⇒ (dim A)) (𝔻⊢ (dim A))) (sc Γ⊢χt (𝕊⊢ (S (dim A))) (trT A=⇒[γt] Γ⊢u:A) idp) ^) >> ap (λ n → (n⇒ (dim A) [ < (< Pre-χ A , n ↦ t > ), S n ↦ u > ]Pre-Ty)) (𝕊-length (dim A))) idp idp

    χ : ∀ {Γ} → Ty Γ → Σ ℕ λ n → Sub Γ (𝕊 n)
    χ (A , Γ⊢A) = dim A , (Pre-χ A , χ Γ⊢A ⊢)

    dim-Ty-n : ∀ {Γ} (n : ℕ) → (γ : Sub Γ (𝕊 n)) → dim (fst (Ty-n {Γ} (n , γ))) == n
    dim-Ty-n n (γ , Γ⊢γ:Sn) = dim[] (n⇒ n) γ >> (dim⇒ n)

    trS-sph : ∀ {Γ n m} → (p : n == m) → {γ : Sub Γ (𝕊 n)} → {δ : Sub Γ (𝕊 m)} → fst γ == fst δ → transport p γ == δ
    trS-sph {Γ} {n} {m} idp {γ} {δ} x = eqS {Γ} {𝕊 m} γ δ x

    Pre-χTy-n : ∀ {Γ} (n : ℕ) → (γ : Sub Γ (𝕊 n)) → Pre-χ (fst (Ty-n {Γ} (n , γ))) == fst γ
    Pre-χTy-n O (.<> , (es _)) = idp
    Pre-χTy-n {Γ} (S n) (< < γ , _ ↦ t > , _ ↦ u > , (sc (sc Γ⊢γ:Sn _ Γ⊢t:A idp) _ Γ⊢u:A idp))
     with eqdecℕ (n-src n) (S (C-length (Pre-𝕊 n))) | eqdecℕ (n-src n) (C-length (Pre-𝕊 n)) | eqdecℕ (S (n-src n)) (S (C-length (Pre-𝕊 n)))
    ...                                     | inl contra | _ | _ =
                                              ⊥-elim (n≠Sn _ (𝕊-length _ >> contra))
    ...                                     | inr _ | inr n≠n | _ =
                                              ⊥-elim (n≠n ((𝕊-length _) ^))
    ...                                     | inr _ | inl _ | inr n≠n = ⊥-elim (n≠n (ap S ((𝕊-length _) ^)))
    ...                                     | inr _ | inl _ | inl _ =
      let χTm-n = (sc Γ⊢γ:Sn (𝔻⊢ n) Γ⊢t:A idp) in
      <,>= (<,>=
      (ap Pre-χ (wk[]T (wkT (𝕊⊢⇒ n) (𝔻⊢ n)) (sc χTm-n (𝕊⊢ (S n)) Γ⊢u:A idp) >> wk[]T (𝕊⊢⇒ n) χTm-n) >> Pre-χTy-n {Γ} n (γ , Γ⊢γ:Sn))
      ((ap n-src (dim[] (n⇒ n) _ >> (dim⇒ n))) >> ((𝕊-length n) ^))
      idp)
      (S= (ap n-src (dim[] (n⇒ n) _ >> (dim⇒ n))) >> ap S ((𝕊-length n) ^))
      idp

    χTy-n : ∀ {Γ} (n : ℕ) → (γ : Sub Γ (𝕊 n)) → χ {Γ} (Ty-n {Γ} (n , γ)) == (n , γ)
    χTy-n {Γ} n γ = Σ= (dim-Ty-n {Γ} n γ) (trS-sph {Γ} (dim-Ty-n {Γ} n γ) {snd (χ {Γ} (Ty-n {Γ} (n , γ)))} {γ} (Pre-χTy-n {Γ} n γ))

  Ty-classifier : ∀ Γ → is-equiv (Ty-n {Γ})
  is-equiv.g (Ty-classifier Γ) (A , Γ⊢A) = χ {Γ} (A , Γ⊢A)
  is-equiv.f-g (Ty-classifier Γ) (A , Γ⊢A) = Σ= (⇒[χ Γ⊢A ] ^) (has-all-paths-⊢T _ _)
  is-equiv.g-f (Ty-classifier Γ) (n , γ) = χTy-n {Γ} n γ
  is-equiv.adj (Ty-classifier Γ) (n , γ) = (is-prop-has-all-paths (is-set-Ty Γ _ _)) _ _
