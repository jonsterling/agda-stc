{-# OPTIONS --cubical --rewriting --confluence-check #-}

module Gluing where

open import Prelude


{-# NO_UNIVERSE_CHECK #-}
record desc ℓ (ϕ : ℙ) : Set (lsuc ℓ) where
  constructor mk-desc
  field
    base : Set ℓ
    part : Partial ϕ (isom base)

module _ {ℓ} (ϕ : ℙ) (D : desc ℓ ϕ) where

  postulate
    realign : isom (desc.base D) [ ϕ ↦ desc.part D ]

    realign/fwd-bwd : (x : _) → iso.fwd (snd ⌈ realign ⌉) (iso.bwd (snd ⌈ realign ⌉) x) ≣ x
    realign/bwd-fwd : (x : fst (⌈ realign ⌉)) → iso.bwd (snd (⌈ realign ⌉)) (iso.fwd (snd (⌈ realign ⌉)) x) ≣ x
    {-# REWRITE realign/fwd-bwd #-}

  [realign/tp] : Set ℓ [ ϕ ↦ (λ z → fst (desc.part D z)) ]
  [realign/tp] = ⌊ fst ⌈ realign ⌉ ⌋

  realign/tp : Set ℓ
  realign/tp = fst ⌈ realign ⌉
