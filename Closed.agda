{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check #-}

module Closed where

open import Prelude

postulate
  _*_ : ∀ (ϕ : I) (A : Type) → Type

module _ {ϕ : I} {A : Type} where
  postulate
    */pt : Partial ϕ (ϕ * A)
    [*/ret] : A → ϕ * A [ ϕ ↦ */pt ]

  */ret : A → ϕ * A
  */ret a = outS ([*/ret] a)

  postulate
    */glue
      : (B : _*_ ϕ A → Type)
      → (u : PartialP ϕ (λ z → B (*/pt z)))
      → (v : (x : A) → B (*/ret x) [ ϕ ↦ (λ {(ϕ = i1) → u _}) ])
      → (x : ϕ * A)
      → B x

    */glue/β
      : (B : _*_ ϕ A → Type)
      → (u : PartialP ϕ (λ z → B (*/pt z)))
      → (v : (x : A) → B (*/ret x) [ ϕ ↦ (λ {(ϕ = i1) → u _}) ])
      → (x : A)
      → */glue B u v (*/ret x) ≣ outS (v x)
    {-# REWRITE */glue/β #-}
