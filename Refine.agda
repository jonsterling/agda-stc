{-# OPTIONS --type-in-type --cubical --rewriting --postfix-projections --with-K #-}

module Refine where

open import Prelude
open import Closed
open import Gluing

module Refine (ϕ : ℙ) (A : ϕ ⊢ Set) (B : (ϕ ⊩ A) → Set\ ϕ lzero) where
  D : desc _ ϕ
  D =
    mk-desc
    (Σ (wrap (ϕ ⊩ A)) λ x → ⌈ B (unwrap x) ⌉)
    λ where
    (ϕ = ⊤) →
      A ⋆ ,
      mk-iso
        (λ x → (mk-wrap (λ _ → x)) , <>)
        (λ x → x .fst .unwrap ⋆)
        (λ x → refl)
        (λ x → refl)

  module Realignment = Realign ϕ D
  open Realignment public hiding (intro)

  intro : (x : ϕ ⊩ A) → ⌈ B x ⌉ → tp
  intro x y = Realignment.intro ((mk-wrap x) , y)

  unrefine : tp → ϕ ⊩ A
  unrefine x = Realignment.elim x .fst .unwrap

  refinement : (x : tp) → ⌈ B (unrefine x) ⌉
  refinement x = Realignment.elim x .snd
