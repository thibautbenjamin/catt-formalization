{-# OPTIONS --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
open import GSeTT.CwF-structure
open import Sets ℕ eqdecℕ
open import CaTT.Ps-contexts

{- batanin trees -}
module CaTT.Trees where
  data tree : Set where
    node : tree
    gr : tree → tree → tree

  -- In order to define the translation from trees to ps-ctx, we need suspension and wedge of ps-ctx

  -- Suspension on ctx
  Susp-Pre-Ctx : Pre-Ctx → Pre-Ctx
  Susp-Pre-Ty : Pre-Ty → Pre-Ty
  Susp-Pre-Tm : Pre-Tm → Pre-Tm

  Susp-Pre-Ctx nil = (nil :: (0 , ∗)) :: (1 , ∗)
  Susp-Pre-Ctx (pctx :: (n , ty)) = Susp-Pre-Ctx pctx :: ((S (S n)) , Susp-Pre-Ty ty)
  Susp-Pre-Ty ∗ = (Var 0) ⇒[ ∗ ] (Var 1)
  Susp-Pre-Ty (u ⇒[ ty ] v) = (Susp-Pre-Tm u) ⇒[ Susp-Pre-Ty ty ] (Susp-Pre-Tm v)
  Susp-Pre-Tm (Var n) = Var (S (S n))

  -- Lemmas on suspension
  Susp-length : ∀ {Γ : Pre-Ctx} → S (S (length Γ)) == length (Susp-Pre-Ctx Γ)
  Susp-length {nil} = idp
  Susp-length {_ :: _} = ap S Susp-length

  -- Derivation for the suspension
  Susp-ps-der : ∀ {Γ n ty} → Γ ⊢ps n # ty → (Susp-Pre-Ctx Γ) ⊢ps (S (S n)) # (Susp-Pre-Ty ty)
  Susp-ps-der pss = pse pss idp idp idp idp idp
  Susp-ps-der (psd x) = psd (Susp-ps-der x)
  Susp-ps-der (pse x idp idp idp idp idp) = pse (Susp-ps-der x) Susp-length (ap S Susp-length) idp idp idp

  -- Suspension on ps-ctx
  Susp : ps-ctx → ps-ctx
  Susp (Γ , ps (Γ⊢ps)) = Susp-Pre-Ctx Γ , ps (psd (Susp-ps-der Γ⊢ps))

  -- Wedge of ctx
  wedge-Pre-Ctx : ℕ → Pre-Ctx → Pre-Ctx → Pre-Ctx
  wedge-Pre-Ty : ℕ → Pre-Ctx → Pre-Ty → Pre-Ty
  wedge-Pre-Tm : ℕ → Pre-Ctx → Pre-Tm → Pre-Tm
  wedge-index : ℕ → Pre-Ctx → ℕ → ℕ

  wedge-Pre-Ctx base Γ nil = Γ
  wedge-Pre-Ctx base Γ (nil :: (n , A)) = Γ
  wedge-Pre-Ctx base Γ (Δ :: (n , A)) = (wedge-Pre-Ctx base Γ Δ) :: (length (wedge-Pre-Ctx base Γ Δ) , wedge-Pre-Ty base Γ A)
  wedge-Pre-Ty base Γ ∗ = ∗
  wedge-Pre-Ty base Γ (u ⇒[ A ] v) = wedge-Pre-Tm base Γ u ⇒[ wedge-Pre-Ty base Γ A ] wedge-Pre-Tm base Γ v
  wedge-Pre-Tm base Γ (Var x) = Var (wedge-index base Γ x)
  wedge-index base Γ O = base
  wedge-index base Γ (S n) = length Γ +ℕ n

  tree-to-Pre-Ctx : tree → Pre-Ctx
  tree-to-Pre-Ctx node = nil :: (0 , ∗)
  tree-to-Pre-Ctx (gr t1 t2) = wedge-Pre-Ctx 1 (Susp-Pre-Ctx (tree-to-Pre-Ctx t1))  (tree-to-Pre-Ctx t2)

  ps-not-nil : ∀ {Γ n A} → Γ ⊢ps n # A → ¬ Γ == nil
  ps-not-nil (psd x) idp = ps-not-nil x idp

  wedge-length : ∀ base Γ Δ a → (length (wedge-Pre-Ctx base Γ (Δ :: a))) == (length Γ +ℕ length Δ)
  wedge-length base Γ nil a = (n+0 (length Γ))^
  wedge-length base Γ (Δ :: a₁) a = S= (wedge-length base Γ Δ _) >> ((n+Sm (length Γ) (length Δ)) ^)

  wedge-ps-der : ∀ {Γ Δ : Pre-Ctx} {n k : ℕ} {A : Pre-Ty} → Γ ⊢ps n # ∗ → Δ ⊢ps k # A → wedge-Pre-Ctx n Γ Δ ⊢ps (wedge-index n Γ k) # (wedge-Pre-Ty n Γ A)
  wedge-ps-der {Γ} {_} {n} {k} Γ⊢psn pss = Γ⊢psn
  wedge-ps-der {Γ} {_} {n} {k} Γ⊢psn (psd x) = psd (wedge-ps-der Γ⊢psn x)
  wedge-ps-der {Γ} {(nil :: (_ , _)) :: (_ , _)} {n} {k} Γ⊢psn (pse (psd x) idp idp idp idp idp) = ⊥-elim (ps-not-nil x idp)
  wedge-ps-der {Γ} {((Δ :: a) :: (_ , _)) :: (_ , _)} {n} {k} Γ⊢psn (pse x idp idp idp idp idp) =
    transport₃
      {D = λ x y z → x ⊢ps y # z}
      (ap² (_::_) idp (ap² (_,_) idp (⇒= idp idp (Var= (wedge-length n Γ Δ a)))))
      (S= (wedge-length n Γ Δ a) >> ((n+Sm (length Γ) (length Δ)) ^) )
      (⇒= idp idp (Var= (wedge-length n Γ Δ a)))
      (pse (wedge-ps-der Γ⊢psn x) idp idp idp idp idp)

  wedge-ctx-der : ∀ {Γ Δ : Pre-Ctx} {n : ℕ} → Γ ⊢t (Var n) # ∗ → Δ ⊢C → wedge-Pre-Ctx n Γ Δ ⊢C
  wedge-ty-der : ∀ {Γ Δ : Pre-Ctx} {n : ℕ} {A : Pre-Ty} → Γ ⊢t (Var n) # ∗ → Δ ⊢T A → wedge-Pre-Ctx n Γ Δ ⊢T wedge-Pre-Ty n Γ A
  wedge-tm-der : ∀ {Γ Δ : Pre-Ctx} {n : ℕ} {A : Pre-Ty} {t : Pre-Tm} → Γ ⊢t (Var n) # ∗ → Δ ⊢t t # A → wedge-Pre-Ctx n Γ Δ ⊢t wedge-Pre-Tm n Γ t # wedge-Pre-Ty n Γ A
  ∈-wedge : ∀ {Γ Δ : Pre-Ctx} {n k : ℕ} {A : Pre-Ty} → Γ ⊢t (Var n) # ∗ → Δ ⊢C → k # A ∈ Δ → wedge-index n Γ k # wedge-Pre-Ty n Γ A ∈ wedge-Pre-Ctx n Γ Δ

  wedge-ctx-der Γ⊢ ec = Γ⊢t:A→Γ⊢ Γ⊢
  wedge-ctx-der Γ⊢ (cc {nil} Δ⊢ Δ⊢A idp) = Γ⊢t:A→Γ⊢ Γ⊢
  wedge-ctx-der Γ⊢ (cc {Δ :: a} Δ⊢ Δ⊢A idp) = cc (wedge-ctx-der Γ⊢ Δ⊢) (wedge-ty-der Γ⊢ Δ⊢A) idp

  wedge-ty-der Γ⊢ (ob Δ⊢) = ob (wedge-ctx-der Γ⊢ Δ⊢)
  wedge-ty-der Γ⊢ (ar Δ⊢A Δ⊢t Δ⊢u) = ar (wedge-ty-der Γ⊢ Δ⊢A) (wedge-tm-der Γ⊢ Δ⊢t) (wedge-tm-der Γ⊢ Δ⊢u)

  wedge-tm-der Γ⊢ (var Δ⊢ x∈Δ) = var (wedge-ctx-der Γ⊢ Δ⊢) (∈-wedge Γ⊢ Δ⊢ x∈Δ)

  ∈-wedge {Γ} {(Δ :: a₁) :: a} {n} {k} {A} Γ⊢ (cc Δ⊢ _ _) (inl x∈Δ) = inl (∈-wedge Γ⊢ Δ⊢ x∈Δ)
  ∈-wedge {Γ} {nil :: a} {n} {k} {A} (var Γ⊢ n∈Γ) (cc ec (ob ec) idp) (inr (idp , idp)) = n∈Γ
  ∈-wedge {Γ} {nil :: a} {n} {k} {A} Γ⊢ (cc ec (ar _ (var _ ()) _) idp) (inr (idp , idp))
  ∈-wedge {Γ} {(Δ :: a₁) :: a} {n} {k} {A} Γ⊢ (cc Δ⊢ x idp) (inr (idp , idp)) = inr (((wedge-length n Γ Δ a₁)^) , idp)

  tree-to-ps-der : ∀ (T : tree) → tree-to-Pre-Ctx T ⊢ps
  tree-to-ps-der node = ps pss
  tree-to-ps-der (gr T₁ T₂) with tree-to-ps-der T₁ , tree-to-ps-der T₂
  ...                       | ps x , ps y = ps (wedge-ps-der (psd (Susp-ps-der x)) y)

  tree-to-ps : ∀ (T : tree) → ps-ctx
  tree-to-ps T = tree-to-Pre-Ctx T , tree-to-ps-der T

  bdryᵢ : ℕ → tree → tree
  bdryᵢ O _ = node
  bdryᵢ (S n) node = node
  bdryᵢ (S n) (gr T T₁) = gr (bdryᵢ n T) (bdryᵢ (S n) T₁)

  dim-tree : tree → ℕ
  dim-tree node = 0
  dim-tree (gr T T₁) = max (S (dim-tree T)) (dim-tree T₁)

  bdry : ∀ (T : tree) → T ≠ node → tree
  bdry node x = ⊥-elim (x idp)
  bdry (gr T T₁) _ = bdryᵢ (pred (dim-tree (gr T T₁))) (gr T T₁)

  wedge:: : ∀ {Γ Δ} {base} {A} → Δ ≠ nil →
    (wedge-Pre-Ctx base Γ (Δ :: (length (wedge-Pre-Ctx base Γ Δ) , A))) == ((wedge-Pre-Ctx base Γ Δ) :: (length (wedge-Pre-Ctx base Γ Δ) , (wedge-Pre-Ty base Γ A)))
  wedge:: {Γ} {nil} {base} {A} Δ≠nil = ⊥-elim (Δ≠nil idp)
  wedge:: {Γ} {Δ :: a} {base} {A} x = ::= idp idp

  wedge-Pre-Sub : ℕ → ℕ → Pre-Sub → Pre-Sub → Pre-Sub
  wedge-Pre-Sub _ _  γ nil = γ
  wedge-Pre-Sub base i γ (nil :: (x , Var y)) = γ
  wedge-Pre-Sub base i γ (γ' :: (x , Var O)) = wedge-Pre-Sub base i γ γ' :: ((x +ℕ (length (wedge-Pre-Sub base i γ γ'))) , Var base)
  wedge-Pre-Sub base i γ (γ' :: (x , Var (S y))) = wedge-Pre-Sub base i γ γ' :: ((x +ℕ (length (wedge-Pre-Sub base i γ γ'))) , Var (y +ℕ i))

  wkS-wedge : ∀{Γ Δ Δ'} {γ} {base} → Δ ⊢S γ > Γ → Δ ⊢t (Var base) # ∗ → Δ' ⊢C → wedge-Pre-Ctx base Δ Δ' ⊢S γ > Γ
  wkS-wedge Δ⊢γ Δ⊢pt ec = Δ⊢γ
  wkS-wedge {Γ} {Δ} {nil :: a} Δ⊢γ Δ⊢pt (cc Δ'⊢ Δ'⊢A idp) = Δ⊢γ
  wkS-wedge {Γ} {Δ} {(Δ' :: a₁) :: a} Δ⊢γ Δ⊢pt (cc Δ'⊢ Δ'⊢A idp) = wkS (wkS-wedge Δ⊢γ Δ⊢pt Δ'⊢ ) ((wedge-ctx-der Δ⊢pt (cc Δ'⊢ Δ'⊢A idp)))

  wedge-π₁-Pre : ℕ → Pre-Ctx → Pre-Ctx → Pre-Sub
  wedge-π₁-Pre n Γ nil = Pre-id Γ
  wedge-π₁-Pre n Γ (Γ' :: _) = wedge-π₁-Pre n Γ Γ'

  wedge-π₂-Pre : ℕ → Pre-Ctx → Pre-Ctx → Pre-Sub
  wedge-π₂-Pre n Γ nil = nil
  wedge-π₂-Pre n Γ (Δ :: (O , A)) = (wedge-π₂-Pre n Γ Δ) :: (O , Var n)
  wedge-π₂-Pre n Γ (Δ :: (S k , A)) = (wedge-π₂-Pre n Γ Δ) :: (S k , Var (k +ℕ length Γ))

  wedge-π₁ : ∀{Γ Γ' base} → Γ ⊢t (Var base) # ∗ → Γ' ⊢C → wedge-Pre-Ctx base Γ Γ' ⊢S (wedge-π₁-Pre base Γ Γ') > Γ
  wedge-π₁ Γ⊢pt ec = Γ⊢id:Γ (Γ⊢t:A→Γ⊢ Γ⊢pt)
  wedge-π₁ Γ⊢pt (cc Γ'⊢@ec Γ'⊢A idp) = Γ⊢id:Γ (Γ⊢t:A→Γ⊢ Γ⊢pt)
  wedge-π₁ Γ⊢pt Γ'+⊢@(cc Γ'⊢@(cc _ _ _) Γ'⊢A idp) = wkS (wedge-π₁ Γ⊢pt Γ'⊢) (wedge-ctx-der Γ⊢pt Γ'+⊢)

  ¬nil⊢t : ∀ {t A} → ¬ (nil ⊢t t # A)
  ¬nil⊢t (var ec ())

  nil⊢A→A=∗ : ∀ {A} → nil ⊢T A → A == ∗
  nil⊢A→A=∗ (ob _) = idp
  nil⊢A→A=∗ (ar A t u) = ⊥-elim (¬nil⊢t (t))

  [π₂]Pre-Ty : ∀ {Γ Γ' base A} → Γ ⊢t (Var base) # ∗ → Γ' ⊢T A → (wedge-Pre-Ty base Γ A) == (A [ wedge-π₂-Pre base Γ Γ' ]Pre-Ty)
  [π₂]Pre-Tm : ∀ {Γ Γ' base t A} → Γ ⊢t (Var base) # ∗ → Γ' ⊢t t # A → (wedge-Pre-Tm base Γ t) == (t [ wedge-π₂-Pre base Γ Γ' ]Pre-Tm)

  [π₂]Pre-Ty {Γ} {nil} Γ⊢pt (ob x) = idp
  [π₂]Pre-Ty {Γ} {nil} Γ⊢pt (ar Γ'⊢A (var _ ()) _)
  [π₂]Pre-Ty {Γ} {Γ' :: a} Γ⊢pt (ob x) = idp
  [π₂]Pre-Ty {Γ} {Γ' :: a} Γ⊢pt (ar Γ'⊢A Γ'⊢t Γ'⊢u) =
    ⇒= ([π₂]Pre-Ty Γ⊢pt Γ'⊢A) ([π₂]Pre-Tm Γ⊢pt Γ'⊢t) ([π₂]Pre-Tm Γ⊢pt Γ'⊢u)

  [π₂]Pre-Tm {Γ} Γ⊢pt (var {x = x} (cc {x = S n} Γ'⊢ Γ'⊢A eq) (inl x₁)) with eqdecℕ x (S n)
  ... | inl idp = Var= (n+m=m+n (length Γ) n)
  ... | inr _ = [π₂]Pre-Tm Γ⊢pt (var Γ'⊢ x₁)
  [π₂]Pre-Tm Γ⊢pt (var {x = O} (cc {Γ'} {_} {A} Γ'⊢ x₂ eq) (inr (idp , idp))) = idp
  [π₂]Pre-Tm {Γ} Γ⊢pt (var {x = S n} (cc {Γ'} {_} {A} Γ'⊢ x₂ eq) (inr (idp , idp))) with eqdecℕ (S n) (S n)
  ... | inl _ = Var= (n+m=m+n (length Γ) n)
  ... | inr contra = ⊥-elim (contra idp)
  [π₂]Pre-Tm {Γ} Γ⊢pt (var (cc {nil} {x = O} Γ'⊢ x₂ eq) (inl ()))
  [π₂]Pre-Tm {Γ} Γ⊢pt (var (cc {Γ' :: a} {x = O} Γ'⊢ x₂ ()) (inl x₁))

  wedge-π₂ : ∀{Γ Γ' base} → Γ ⊢t (Var base) # ∗ → Γ' ⊢C → wedge-Pre-Ctx base Γ Γ' ⊢S (wedge-π₂-Pre base Γ Γ') > Γ'
  wedge-π₂ Γ⊢pt ec = es (Γ⊢t:A→Γ⊢ Γ⊢pt)
  wedge-π₂ Γ⊢pt Γ'⊢@(cc ec (ob x) idp) = sc (es (Γ⊢t:A→Γ⊢ Γ⊢pt)) Γ'⊢ Γ⊢pt idp
  wedge-π₂ Γ⊢pt Γ'⊢@(cc ec (ar _ (var _ ()) _) idp)
  wedge-π₂ {Γ} {(Δ :: _) :: _} Γ⊢pt Γ'+⊢@(cc Γ'⊢@(cc _ _ _) x idp) =
    sc (wkS (wedge-π₂ Γ⊢pt Γ'⊢) (wedge-ctx-der Γ⊢pt Γ'+⊢))
      Γ'+⊢
      (transport₃ {D = _⊢t_#_}
                  idp
                  (Var= (n+m=m+n (length Γ) (length Δ)))
                  ([π₂]Pre-Ty Γ⊢pt x)
                  (wedge-tm-der Γ⊢pt (Γ,x:A⊢→Γ,x:A⊢x:A Γ'+⊢))) idp

  wedge-up-Pre : ℕ → Pre-Sub → Pre-Sub → Pre-Sub
  wedge-up-Pre base γ nil = γ
  wedge-up-Pre base γ (nil :: a) = γ
  wedge-up-Pre base γ (γ' :: (_ , A)) = wedge-up-Pre base γ γ' :: (length (wedge-up-Pre base γ γ') , A)

  wedge-up : ∀{Γ Γ' Δ γ γ' base} → Γ ⊢t (Var base) # ∗ → Δ ⊢S γ > Γ → Δ ⊢S γ' > Γ' → ((Var base) [ γ ]Pre-Tm) == ((Var 0) [ γ' ]Pre-Tm) → Δ ⊢S wedge-up-Pre base γ γ' > wedge-Pre-Ctx base Γ Γ'
  wedge-up Γ⊢pt Δ⊢γ (es x) _ = Δ⊢γ
  wedge-up Γ⊢pt Δ⊢γ (sc {γ = nil} (es _) _ _ idp) eq = Δ⊢γ
  wedge-up Γ⊢pt Δ⊢γ Δ⊢γ'+@(sc {γ = γ' :: a} Δ⊢γ'@(sc _ _ _ _) x x₁ idp) eq = sc (wedge-up Γ⊢pt Δ⊢γ Δ⊢γ' {!!}) (wedge-ctx-der Γ⊢pt (Δ⊢γ:Γ→Γ⊢ Δ⊢γ'+)) {!!} {!!}

  -- [wedge]T : ∀ {Γ Δ A γ δ base} → Δ ⊢T A → ((wedge-Pre-Ty base Γ A) [ wedge-Pre-Sub base (length Δ) γ δ ]Pre-Ty) == wedge-Pre-Ty base Δ (A [ δ ]Pre-Ty)
  -- [wedge]t : ∀ {Γ Δ t A γ δ base} → Δ ⊢t t # A → ((wedge-Pre-Tm base Γ t) [ wedge-Pre-Sub base (length Δ) γ δ ]Pre-Tm) == wedge-Pre-Tm base Δ (t [ δ ]Pre-Tm)

  -- [wedge]T (ob _) = idp
  -- [wedge]T (ar Δ⊢A Δ⊢t Δ⊢u) = ⇒= ([wedge]T Δ⊢A) ([wedge]t Δ⊢t) ([wedge]t Δ⊢u)
  -- [wedge]t {δ = nil} (var Δ⊢ x∈Δ) = {!!}
  -- [wedge]t {δ = δ :: a} (var Δ⊢ x∈Δ) = {!δ!}


  wedge-sub-der : ∀{Γ Δ Γ' Δ'} {γ γ'} {base-src base-tgt : ℕ} →
    Δ ⊢S γ > Γ →
    Δ' ⊢S γ' > Γ' →
    Γ ⊢t (Var base-src) # ∗ →
    Δ ⊢t (Var base-tgt) # ∗ →
    ((Var base-tgt) [ γ ]Pre-Tm) == Var base-src →
    ((Var 0) [ γ' ]Pre-Tm) == Var 0 →
    (wedge-Pre-Ctx base-tgt Δ Δ') ⊢S wedge-Pre-Sub base-tgt ((length Δ)) γ γ' > (wedge-Pre-Ctx base-src Γ Γ')
  wedge-sub-der Δ⊢γ:Γ (es x) Γ⊢pt Δ⊢pt eq idp = wkS-wedge Δ⊢γ:Γ Δ⊢pt x
  wedge-sub-der {γ' = nil :: (x , Var n)} Δ⊢γ:Γ (sc (es Δ'⊢) a x₁ idp) Γ⊢pt Δ⊢pt eq1 eq2 = wkS-wedge Δ⊢γ:Γ Δ⊢pt Δ'⊢
  wedge-sub-der {Γ = Γ} {Γ' = (Γ' :: a) :: _} {γ' = (_ :: _) :: (x , Var O)} Δ⊢γ:Γ (sc Δ'⊢γ':Γ' Γ'+⊢@(cc _ _ idp) Δ'+⊢t idp) Γ⊢pt Δ⊢pt eq1 eq2 = sc (wedge-sub-der Δ⊢γ:Γ Δ'⊢γ':Γ' Γ⊢pt Δ⊢pt eq1 {!!}) (wedge-ctx-der Γ⊢pt Γ'+⊢) {!wedge-tm-der Δ⊢pt Δ'+⊢t!} (wedge-length _ Γ Γ' a >> {!!})
  wedge-sub-der {Γ' = (_ :: _) :: _} {γ' = (_ :: _) :: (x , Var (S n))} Δ⊢γ:Γ (sc Δ'⊢γ':Γ' Δ'+⊢ Δ'+⊢t idp) Γ⊢pt Δ⊢pt eq1 eq2 = sc {!!} {!!} {!!} {!!}


-- transport₃ idp {!!} (wedge:: λ {()}) (sc (wedge-sub-der Δ⊢γ:Γ Δ'⊢γ':Γ' Γ⊢pt Δ⊢pt eq1 {!!}) (wedge-ctx-der Γ⊢pt a) {!wedge-tm-der Γ⊢pt x₁!} {!!})



  -- wedge-sub : ∀{Γ Δ Γ' Δ'} {γ γ'} → ℕ → Δ ⊢S γ > Γ → Δ' ⊢S γ' > Γ' → Pre-Sub
  -- wedge-sub {Γ} {Δ} {Γ'} {Δ'} {γ} {γ'} n Δ⊢γ:Γ (es x) = γ
  -- wedge-sub n Δ⊢γ:Γ (sc {γ = γ'} Δ'⊢γ':Γ' x (var x₁ x₂) idp) = γ' :: {!!}

  srcᵢ-tree : ℕ → tree → Pre-Sub
  srcᵢ-tree O T = nil :: (0 , Var 0)
  srcᵢ-tree (S n) node = nil :: (0 , Var 0)
  srcᵢ-tree (S n) (gr T T₁) = {!wedge-sub (srcᵢ-tree n T) (srcᵢ-tree (S n) T₁)!}

  src-incl-tree : ∀ (T : tree) → Pre-Sub
  src-incl-tree = {!!}

  -- Disks and whiskerings
  𝔻-Tree : ℕ → tree
  𝔻-Tree O = node
  𝔻-Tree (S n) = gr (𝔻-Tree n) node

  left-whisk-Tree : ℕ → tree
  left-whisk-Tree n = gr node (𝔻-Tree n)

  right-whisk-Tree : ℕ → tree
  right-whisk-Tree O = gr node node
  right-whisk-Tree (S n) = gr (𝔻-Tree n) (gr node node)

  left-whisk : ℕ → ps-ctx
  right-whisk : ℕ → ps-ctx

  left-whisk n = tree-to-ps (left-whisk-Tree n)
  right-whisk n = tree-to-ps (right-whisk-Tree n)
