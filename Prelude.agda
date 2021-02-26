{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check #-}

module Prelude where

open import Cubical.Foundations.Prelude hiding (refl) public
open import Agda.Builtin.Equality renaming (_≡_ to _≣_) public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (SSet) public

record iso {ℓ} (A B : Type ℓ) : Type ℓ where
  constructor mk-iso
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → (fwd (bwd x)) ≣ x
    bwd-fwd : ∀ x → (bwd (fwd x)) ≣ x

isom : ∀ {ℓ} (B : Type ℓ) → Type (ℓ-suc ℓ)
isom {ℓ} B = Σ (Type ℓ) λ A → iso A B
