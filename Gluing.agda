{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check #-}

module Gluing where

open import Prelude

{-# NO_UNIVERSE_CHECK #-}
record desc ℓ (ϕ : I) : Type (ℓ-suc ℓ) where
  constructor mk-desc
  field
    base : Type ℓ
    part : Partial ϕ (isom base)

postulate
  realign : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) → isom (desc.base D) [ ϕ ↦ desc.part D ]

  realign/fwd-bwd : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) (x : _) → iso.fwd (snd (outS (realign ϕ D))) (iso.bwd (snd (outS (realign ϕ D))) x) ≣ x
  realign/bwd-fwd : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) (x : fst (outS (realign ϕ D))) → iso.bwd (snd (outS (realign ϕ D))) (iso.fwd (snd (outS (realign ϕ D))) x) ≣ x
  {-# REWRITE realign/fwd-bwd #-}

[realign/tp] : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) → Type ℓ [ ϕ ↦ (λ z → fst (desc.part D z)) ]
[realign/tp] ϕ D = inS (fst (outS (realign ϕ D)))

realign/tp : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) → Type ℓ
realign/tp ϕ D = fst (outS (realign ϕ D))
