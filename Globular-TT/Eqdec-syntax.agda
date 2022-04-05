{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax



{- Type theory for globular sets -}
module Globular-TT.Eqdec-syntax {l}
  (index : Set l) (eqdec-index : eqdec index) where

  open import Globular-TT.Syntax index

  eqdec-Ty : eqdec Pre-Ty
  eqdec-Tm : eqdec Pre-Tm
  eqdec-Sub : eqdec Pre-Sub

  eqdec-Ty ∗ ∗ = inl idp
  eqdec-Ty ∗ (⇒ _ _ _) = inr λ{()}
  eqdec-Ty (⇒ _ _ _ ) ∗ = inr λ{()}
  eqdec-Ty (⇒ A t u) (⇒ B t' u') with eqdec-Ty A B | eqdec-Tm t t' | eqdec-Tm u u'
  ...                            | inl idp | inl idp | inl idp = inl idp
  ...                            | inr A≠B | _ | _ = inr λ{idp → A≠B idp}
  ...                            | inl idp | inr t≠t' | _ = inr λ eq → t≠t' (snd (fst (=⇒ eq)))
  ...                            | inl idp | inl idp | inr u≠u' = inr λ eq → u≠u' (snd (=⇒ eq))
  eqdec-Tm (Var x) (Var y) with eqdecℕ x y
  ...                      | inl idp = inl idp
  ...                      | inr x≠y = inr λ {idp → x≠y idp}
  eqdec-Tm (Var _) (Tm-constructor _ _) = inr λ{()}
  eqdec-Tm (Tm-constructor _ _) (Var _) = inr λ{()}
  eqdec-Tm (Tm-constructor i γ) (Tm-constructor i' γ') with eqdec-index i i' | eqdec-Sub γ γ'
  ...                                                   | inl idp | inl idp = inl idp
  ...                                                   | inr i≠i' | _ = inr λ{idp → i≠i' idp}
  ...                                                   | inl idp | inr γ≠γ' = inr λ eq → γ≠γ' (snd (=Tm-constructor eq))
  eqdec-Sub <> <> = inl idp
  eqdec-Sub < _ , _ ↦ _ > <> = inr λ{()}
  eqdec-Sub <> < _ , _ ↦ _ > = inr λ{()}
  eqdec-Sub < γ , x ↦ t > < γ' , y ↦ t' > with eqdec-Sub γ γ' | eqdecℕ x y | eqdec-Tm t t'
  ...                                      | inl idp | inl idp | inl idp = inl idp
  ...                                      | inr γ≠γ' | _ | _ = inr λ{idp → γ≠γ' idp}
  ...                                      | inl idp | inr x≠y | _ = inr λ eq → x≠y (snd (fst (=<,> eq)))
  ...                                      | inl idp | inl idp | inr t≠t' = inr λ eq → t≠t' (snd (=<,> eq))
