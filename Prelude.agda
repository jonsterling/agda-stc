{-# OPTIONS --cubical --rewriting --confluence-check #-}

module Prelude where

open import Agda.Primitive public
open import Agda.Builtin.Sigma public
open import Agda.Primitive.Cubical public
  renaming (I to ℙ; i0 to ⊥; i1 to ⊤; itIsOne to ⋆)
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public

infix 10 _⊢_
infix 10 _⊩_
_⊢_ = Partial
_⊩_ = PartialP


open import Agda.Builtin.Cubical.Sub public
  renaming (inc to ⌊_⌋; primSubOut to ⌈_⌉)

infix 4 _[_⊢_]
_[_⊢_] = Sub

Sub-syntax = Sub
syntax Sub-syntax A ϕ (λ z → a) = A [ z ∶ ϕ ⊢ a ]



record iso {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor mk-iso
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → (fwd (bwd x)) ≡ x
    bwd-fwd : ∀ x → (bwd (fwd x)) ≡ x

open iso public

isom : ∀ {ℓ} (B : Set ℓ) → Set (lsuc ℓ)
isom {ℓ} B = Σ (Set ℓ) λ A → iso A B
