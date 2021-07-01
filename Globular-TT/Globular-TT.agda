{-# OPTIONS --without-K #-}

open import Prelude
import GSeTT.Typed-Syntax
import Globular-TT.Syntax
import Globular-TT.Rules

module Globular-TT.Globular-TT {l} (index : Set l) (rule : index → GSeTT.Typed-Syntax.Ctx × (Globular-TT.Syntax.Pre-Ty index))
                                                   (assumption : Globular-TT.Rules.well-founded index rule)
                                                   (eqdec-index : eqdec index)
                                                   where

  open import Globular-TT.Syntax index
  open import Globular-TT.Eqdec-syntax index eqdec-index
  open import Globular-TT.Rules index rule
  open import Globular-TT.CwF-Structure index rule
  open import Globular-TT.Uniqueness-Derivations index rule eqdec-index
  open import Globular-TT.Disks index rule eqdec-index
  open import Globular-TT.Typed-Syntax index rule eqdec-index
  open import Globular-TT.Dec-Type-Checking index rule assumption eqdec-index
