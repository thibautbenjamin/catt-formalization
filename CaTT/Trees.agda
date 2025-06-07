{-# OPTIONS --without-K #-}

open import Prelude
open import GSeTT.Syntax
open import GSeTT.Rules
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

  wedge-sub : ∀{Γ Δ Γ' Δ'} {γ γ'} → ℕ → Δ ⊢S γ > Γ → Δ' ⊢S γ' > Γ' → Pre-Sub
  wedge-sub {Γ} {Δ} {Γ'} {Δ'} {γ} {γ'} n Δ⊢γ:Γ (es x) = γ
  wedge-sub n Δ⊢γ:Γ (sc {γ = γ'} Δ'⊢γ':Γ' x (var x₁ x₂) idp) = γ' :: {!!}

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
