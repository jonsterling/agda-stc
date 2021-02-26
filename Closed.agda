{-# OPTIONS --cubical --rewriting --confluence-check #-}

module Closed where

open import Prelude

private
  variable
    ℓ ℓ′ : Level

postulate
  _*_ : ∀ (ϕ : ℙ) (A : Set ℓ) → Set ℓ

module _ {ϕ : ℙ} {A : Set ℓ} where
  postulate
    */pt : Partial ϕ (ϕ * A)
    [*/ret] : A → ϕ * A [ ϕ ⊢ */pt ]

  */ret : A → ϕ * A
  */ret a = ⌈ [*/ret] a ⌉

  module _ (B : ϕ * A → Set ℓ′) (u : PartialP ϕ (λ z → B (*/pt z))) (v : (x : A) → B (*/ret x) [ ϕ ⊢ (λ {(ϕ = ⊤) → u _}) ]) where
    postulate
      */glue : (x : ϕ * A) → B x
      */glue/β : (x : A) → */glue (*/ret x) ≡ ⌈ v x ⌉
      {-# REWRITE */glue/β #-}
