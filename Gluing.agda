{-# OPTIONS --cubical --rewriting #-}

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
    realign : isom (desc.base D) [ ϕ ⊢ desc.part D ]

  realign/fwd-bwd : (x : _) → fwd (snd ⌈ realign ⌉) (bwd (snd ⌈ realign ⌉) x) ≡ x
  realign/fwd-bwd = fwd-bwd (snd ⌈ realign ⌉)
  {-# REWRITE realign/fwd-bwd #-}

  realign/bwd-fwd : (x : fst (⌈ realign ⌉)) → bwd (snd (⌈ realign ⌉)) (fwd (snd (⌈ realign ⌉)) x) ≡ x
  realign/bwd-fwd = bwd-fwd (snd ⌈ realign ⌉)

  [realign/tp] : Set ℓ [ z ∶ ϕ ⊢ fst (desc.part D z) ]
  [realign/tp] = ⌊ fst ⌈ realign ⌉ ⌋

  realign/tp : Set ℓ
  realign/tp = fst ⌈ realign ⌉
