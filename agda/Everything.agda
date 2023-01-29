{-
Maycon Amaro, 2021. Federal University of Ouro Preto.

Some notes:
  ∙ Typecheck this file to typecheck everything
  ∙ You can run a grep or similiar  in the project
    to confirm no TERMINATING pragma or postulates
    are used on any file.
  ∙ This was typechecked with
    - Agda 2.6.2.1
    - Standard Library 1.7.1
    - Kubuntu 21.10 (impish)
-}

{-# OPTIONS --safe #-}

open import Common.Type
open import Common.Context
open import Common.Fuel

open import R.Syntax.Base
open import R.Syntax.IR
open import R.Syntax.IR.Properties
open import R.Syntax.Properties
open import R.Syntax.Unrolling
open import R.Syntax
open import R.Semantics
open import R.Semantics.Definitional

open import L.Syntax
open import L.Syntax.Properties
open import L.Semantics
open import L.Semantics.Definitional

open import Transform.Translation

open import Examples.Context
open import Examples.R
open import Examples.L
open import Examples.Translation
