{-# OPTIONS --cubical --rewriting --confluence-check #-}

module Closed where

open import Prelude

private
  variable
    ℓ ℓ′ : Level

postulate
  _*_ : ∀ (ϕ : I) (A : Type ℓ) → Type ℓ

module _ {ϕ : I} {A : Type ℓ} where
  postulate
    */pt : Partial ϕ (ϕ * A)
    [*/ret] : A → ϕ * A [ ϕ ↦ */pt ]

  */ret : A → ϕ * A
  */ret a = outS ([*/ret] a)

  module _ (B : ϕ * A → Type ℓ′) (u : PartialP ϕ (λ z → B (*/pt z))) (v : (x : A) → B (*/ret x) [ ϕ ↦ (λ {(ϕ = i1) → u _}) ]) where
    postulate
      */glue : (x : ϕ * A) → B x
      */glue/β : (x : A) → */glue (*/ret x) ≣ outS (v x)
      {-# REWRITE */glue/β #-}
