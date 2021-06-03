{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import Agda.Primitive
open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.Uniqueness-Derivations

{- Disk and Sphere contexts - properties -}
module GSeTT.Disks where

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
  𝕊 : ℕ → Pre-Ctx
  𝔻 : ℕ → Pre-Ctx

  𝕊 O = nil
  𝕊 (S n) = (𝔻 n) :: (length (𝔻 n) , n⇒ n)
  𝔻 n = (𝕊 n) :: (length (𝕊 n) , n⇒ n)

  𝕊-length : ∀ n → length (𝕊 n) == n-src n
  𝕊-length O = idp
  𝕊-length (S n) = S= (S= (𝕊-length n))
  {-# REWRITE 𝕊-length #-}

  {- Disk and Sphere context are valid -}
  𝕊⊢ : ∀ n → 𝕊 n ⊢C
  𝔻⊢ : ∀ n → 𝔻 n ⊢C
  𝕊⊢⇒ : ∀ n → 𝕊 n ⊢T n⇒ n

  𝕊⊢ O = ec
  𝕊⊢ (S n) = cc (𝔻⊢ n) (wkT (𝕊⊢⇒ n) (𝔻⊢ n))
  𝔻⊢ n = cc (𝕊⊢ n) (𝕊⊢⇒ n)

  𝕊⊢⇒ O = ob ec
  𝕊⊢⇒ (S n) = ar (wkt (var (𝔻⊢ n) (inr (((𝕊-length n) ^) , idp))) (𝕊⊢ (S n))) (var (𝕊⊢ (S n)) (inr ((S= (𝕊-length n) ^) , idp)))



  {- Spheres classify types and disks classify terms -}
  -- Ty-n : ∀ {Γ} → Σ ℕ (λ n → Σ Pre-Sub (λ γ → Γ ⊢S γ > 𝕊 n)) → Σ Pre-Ty (λ A → (Γ ⊢T A))
  -- Ty-n {Γ} (n , (γ , Γ⊢γ:Sn)) = ((n⇒ n)[ γ ]Pre-Ty) , ([]T (𝕊⊢⇒ n) Γ⊢γ:Sn)


  -- private
  --   χ : Pre-Ty → Pre-Sub

  --   χ ∗ = nil
  --   χ (⇒ A t u) = (χ A :: (n-src (dim A) , t)) :: (n-tgt (dim A) , u)

  --   χ_⊢ : ∀ {Γ A} → (Γ⊢A : Γ ⊢T A) → Γ ⊢S (χ A) > 𝕊 (dim A)
  --   ⇒[χ_] : ∀ {Γ A} → (Γ⊢A : Γ ⊢T A) → A == ((n⇒  (dim A))[ χ A ]Pre-Ty)

  --   χ ob Γ⊢ ⊢ = es Γ⊢
  --   χ_⊢ {Γ} {⇒ A t u} (ar Γ⊢t:A Γ⊢u:A) =
  --     let Γ⊢A = Γ⊢t:A→Γ⊢A Γ⊢t:A in
  --     let Γ⊢χt = sc χ Γ⊢A ⊢ (𝔻⊢ (dim A)) (trT (⇒[χ Γ⊢A ]) Γ⊢t:A) in
  --       sc Γ⊢χt (𝕊⊢ (S (dim A))) (trT (⇒[χ Γ⊢A ] >> (wk[]T (𝕊⊢⇒ (dim A)) Γ⊢χt ^)) Γ⊢u:A)

  --   ⇒[χ_] {Γ} {.∗} (ob _) = idp
  --   ⇒[χ_] {Γ} {(⇒ A t u)} (ar Γ⊢t:A Γ⊢u:A) with eqdecℕ (n-src (dim A)) (n-tgt (dim A)) | eqdecℕ (n-src (dim A)) (n-src (dim A)) | eqdecℕ (S (n-src (dim A))) (S (n-src (dim A)))
  --   ...                                     | inl contra | _ | _ = ⊥-elim (n≠Sn _ contra)
  --   ...                                     | inr _ | inr n≠n | _ = ⊥-elim (n≠n idp)
  --   ...                                     | inr _ | inl _ | inr n≠n = ⊥-elim (n≠n idp)
  --   ...                                     | inr _ | inl _ | inl _ =
  --     let Γ⊢A = (Γ⊢t:A→Γ⊢A Γ⊢t:A) in
  --     let Γ⊢χt = (sc χ Γ⊢A ⊢ (𝔻⊢(dim A)) (trT ⇒[χ Γ⊢A ] Γ⊢t:A)) in
  --     let A=⇒[γt] = ⇒[χ Γ⊢A ] >> (wk[]T (𝕊⊢⇒ (dim A)) Γ⊢χt ^) in
  --     ⇒= (A=⇒[γt] >> (wk[]T (wkT (𝕊⊢⇒ (dim A)) (𝔻⊢ (dim A))) (sc Γ⊢χt (𝕊⊢ (S (dim A))) (trT A=⇒[γt] Γ⊢u:A)) ^)) idp idp

  --   -- TODO : move this at the right place
  --   dim[] : ∀ (A : Pre-Ty) (γ : Pre-Sub) → dim (A [ γ ]Pre-Ty) == dim A
  --   dim[] ∗ γ = idp
  --   dim[] (⇒ A x x₁) γ = S= (dim[] A γ)

  --   dim-Ty-n : ∀ {Γ} (n : ℕ) → (γ : Pre-Sub) → (Γ⊢γ:Sn : Γ ⊢S γ > 𝕊 n) → dim (fst (Ty-n (n , (γ , Γ⊢γ:Sn)))) == n
  --   dim-Ty-n n γ Γ⊢γ:Sn = dim[] (n⇒ n) γ >> (dim⇒ n)

  --   χTy-n : ∀ {Γ} (n : ℕ) → (γ : Pre-Sub) → (Γ⊢γ:Sn : Γ ⊢S γ > 𝕊 n) → χ (fst (Ty-n (n , (γ , Γ⊢γ:Sn)))) == γ
  --   χTy-n O .nil (es _) = idp
  --   χTy-n (S n) ((γ :: (_ , t)) :: (_ , u)) (sc (sc Γ⊢γ:Sn _ Γ⊢t:A) _ Γ⊢u:A) with eqdecℕ (n-src n) (S (n-src n)) | eqdecℕ (n-src n) (n-src n) | eqdecℕ (S (n-src n)) (S (n-src n))
  --   ...                                     | inl contra | _ | _ = ⊥-elim (n≠Sn _ contra)
  --   ...                                     | inr _ | inr n≠n | _ = ⊥-elim (n≠n idp)
  --   ...                                     | inr _ | inl _ | inr n≠n = ⊥-elim (n≠n idp)
  --   ...                                     | inr _ | inl _ | inl _ =
  --     let χTm-n = (sc Γ⊢γ:Sn (𝔻⊢ n) Γ⊢t:A) in
  --     ::= (::= (ap χ (wk[]T (wkT (𝕊⊢⇒ n) (𝔻⊢ n)) (sc χTm-n (𝕊⊢ (S n)) Γ⊢u:A) >> wk[]T (𝕊⊢⇒ n) χTm-n) >> χTy-n n γ Γ⊢γ:Sn)
  --              (×= (ap n-src (dim[] (n⇒ n) _ >> (dim⇒ n))) idp))
  --              (×= (S= (ap n-src (dim[] (n⇒ n) _ >> (dim⇒ n)))) idp)


  -- Ty-classifier : ∀ Γ → is-equiv (Ty-n {Γ})
  -- is-equiv.g (Ty-classifier Γ) (A , Γ⊢A) = dim A , (χ A , (χ Γ⊢A ⊢))
  -- is-equiv.f-g (Ty-classifier Γ) (A , Γ⊢A) = Σ= (⇒[χ Γ⊢A ] ^) {!!} -- TODO : prove and use that this type is a prop
  -- is-equiv.g-f (Ty-classifier Γ) (n , (γ , Γ⊢γ:Sn)) = Σ= (dim-Ty-n n γ Γ⊢γ:Sn) (Σ= {!χTy-n n γ Γ⊢γ:Sn!} {!!})
  -- is-equiv.adj (Ty-classifier Γ) = {!!}
  -- --
  Ty-n : ∀ {Γ} → Σ (ℕ × Pre-Sub) (λ {(n , γ) →  Γ ⊢S γ > 𝕊 n}) → Σ Pre-Ty (λ A → (Γ ⊢T A))
  Ty-n {Γ} ((n , γ), Γ⊢γ:Sn) = ((n⇒ n)[ γ ]Pre-Ty) , ([]T (𝕊⊢⇒ n) Γ⊢γ:Sn)


  private
    χ : Pre-Ty → Pre-Sub

    χ ∗ = nil
    χ (⇒ A t u) = (χ A :: (n-src (dim A) , t)) :: (n-tgt (dim A) , u)

    χ_⊢ : ∀ {Γ A} → (Γ⊢A : Γ ⊢T A) → Γ ⊢S (χ A) > 𝕊 (dim A)
    ⇒[χ_] : ∀ {Γ A} → (Γ⊢A : Γ ⊢T A) → A == ((n⇒  (dim A))[ χ A ]Pre-Ty)

    χ ob Γ⊢ ⊢ = es Γ⊢
    χ_⊢ {Γ} {⇒ A t u} (ar Γ⊢t:A Γ⊢u:A) =
      let Γ⊢A = Γ⊢t:A→Γ⊢A Γ⊢t:A in
      let Γ⊢χt = sc χ Γ⊢A ⊢ (𝔻⊢ (dim A)) (trT (⇒[χ Γ⊢A ]) Γ⊢t:A) in
        sc Γ⊢χt (𝕊⊢ (S (dim A))) (trT (⇒[χ Γ⊢A ] >> (wk[]T (𝕊⊢⇒ (dim A)) Γ⊢χt ^)) Γ⊢u:A)

    ⇒[χ_] {Γ} {.∗} (ob _) = idp
    ⇒[χ_] {Γ} {(⇒ A t u)} (ar Γ⊢t:A Γ⊢u:A) with eqdecℕ (n-src (dim A)) (n-tgt (dim A)) | eqdecℕ (n-src (dim A)) (n-src (dim A)) | eqdecℕ (S (n-src (dim A))) (S (n-src (dim A)))
    ...                                     | inl contra | _ | _ = ⊥-elim (n≠Sn _ contra)
    ...                                     | inr _ | inr n≠n | _ = ⊥-elim (n≠n idp)
    ...                                     | inr _ | inl _ | inr n≠n = ⊥-elim (n≠n idp)
    ...                                     | inr _ | inl _ | inl _ =
      let Γ⊢A = (Γ⊢t:A→Γ⊢A Γ⊢t:A) in
      let Γ⊢χt = (sc χ Γ⊢A ⊢ (𝔻⊢(dim A)) (trT ⇒[χ Γ⊢A ] Γ⊢t:A)) in
      let A=⇒[γt] = ⇒[χ Γ⊢A ] >> (wk[]T (𝕊⊢⇒ (dim A)) Γ⊢χt ^) in
      ⇒= (A=⇒[γt] >> (wk[]T (wkT (𝕊⊢⇒ (dim A)) (𝔻⊢ (dim A))) (sc Γ⊢χt (𝕊⊢ (S (dim A))) (trT A=⇒[γt] Γ⊢u:A)) ^)) idp idp

    -- TODO : move this at the right place
    dim[] : ∀ (A : Pre-Ty) (γ : Pre-Sub) → dim (A [ γ ]Pre-Ty) == dim A
    dim[] ∗ γ = idp
    dim[] (⇒ A x x₁) γ = S= (dim[] A γ)

    dim-Ty-n : ∀ {Γ} (n : ℕ) → (γ : Pre-Sub) → (Γ⊢γ:Sn : Γ ⊢S γ > 𝕊 n) → dim (fst (Ty-n ((n , γ), Γ⊢γ:Sn))) == n
    dim-Ty-n n γ Γ⊢γ:Sn = dim[] (n⇒ n) γ >> (dim⇒ n)

    χTy-n : ∀ {Γ} (n : ℕ) → (γ : Pre-Sub) → (Γ⊢γ:Sn : Γ ⊢S γ > 𝕊 n) → χ (fst (Ty-n ((n , γ), Γ⊢γ:Sn))) == γ
    χTy-n O .nil (es _) = idp
    χTy-n (S n) ((γ :: (_ , t)) :: (_ , u)) (sc (sc Γ⊢γ:Sn _ Γ⊢t:A) _ Γ⊢u:A) with eqdecℕ (n-src n) (S (n-src n)) | eqdecℕ (n-src n) (n-src n) | eqdecℕ (S (n-src n)) (S (n-src n))
    ...                                     | inl contra | _ | _ = ⊥-elim (n≠Sn _ contra)
    ...                                     | inr _ | inr n≠n | _ = ⊥-elim (n≠n idp)
    ...                                     | inr _ | inl _ | inr n≠n = ⊥-elim (n≠n idp)
    ...                                     | inr _ | inl _ | inl _ =
      let χTm-n = (sc Γ⊢γ:Sn (𝔻⊢ n) Γ⊢t:A) in
      ::= (::= (ap χ (wk[]T (wkT (𝕊⊢⇒ n) (𝔻⊢ n)) (sc χTm-n (𝕊⊢ (S n)) Γ⊢u:A) >> wk[]T (𝕊⊢⇒ n) χTm-n) >> χTy-n n γ Γ⊢γ:Sn)
               (×= (ap n-src (dim[] (n⇒ n) _ >> (dim⇒ n))) idp))
               (×= (S= (ap n-src (dim[] (n⇒ n) _ >> (dim⇒ n)))) idp)

  is-set-Ty : ∀ Γ → is-set (Σ Pre-Ty (λ A → Γ ⊢T A))
  is-set-Ty = {!!}

  Ty-classifier : ∀ Γ → is-equiv (Ty-n {Γ})
  is-equiv.g (Ty-classifier Γ) (A , Γ⊢A) = (dim A , χ A), χ Γ⊢A ⊢
  is-equiv.f-g (Ty-classifier Γ) (A , Γ⊢A) = Σ= (⇒[χ Γ⊢A ] ^) (has-all-paths-⊢T _ _)
  is-equiv.g-f (Ty-classifier Γ) ((n , γ), Γ⊢γ:Sn) = Σ= (×= (dim-Ty-n n γ Γ⊢γ:Sn) (χTy-n n γ Γ⊢γ:Sn)) (has-all-paths-⊢S _ _)
  is-equiv.adj (Ty-classifier Γ) ((n , γ) , Γ⊢γ:Sn) = (is-prop-has-all-paths (is-set-Ty Γ _ _)) _ _ 
