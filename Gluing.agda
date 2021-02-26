{-# OPTIONS --cubical --rewriting --with-K #-}

module Gluing where

open import Prelude


{-# NO_UNIVERSE_CHECK #-}
record desc ℓ (ϕ : ℙ) : Set (lsuc ℓ) where
  constructor mk-desc
  field
    base : Set ℓ
    part : Partial ϕ (isom base)

module Realign {ℓ} (ϕ : ℙ) (D : desc ℓ ϕ) where

  postulate
    realign : isom (desc.base D) [ ϕ ⊢ desc.part D ]

  tp = ⌈ realign ⌉ .fst
  base = desc.base D
  rules = ⌈ realign ⌉ .snd
  intro = rules .bwd
  elim = rules .fwd

  beta : (x : base) → fwd (snd ⌈ realign ⌉) (bwd (snd ⌈ realign ⌉) x) ≡ x
  beta = fwd-bwd (snd ⌈ realign ⌉)
  {-# REWRITE beta #-}

  eta : (x : tp) → bwd (snd (⌈ realign ⌉)) (fwd (snd (⌈ realign ⌉)) x) ≡ x
  eta = bwd-fwd (snd ⌈ realign ⌉)
