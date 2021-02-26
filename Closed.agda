{-# OPTIONS --cubical --rewriting --with-K #-}

module Closed where

open import Prelude
open import Gluing

Set\ : (ϕ : ℙ) (ℓ : Level) → _
Set\ ϕ ℓ = Set ℓ [ _ ∶ ϕ ⊢ Unit ]

private
  variable
    ℓ ℓ′ : Level

postulate
  _*_ : (ϕ : ℙ) → (A : Set ℓ) → Set\ ϕ ℓ


module _ {ϕ : ℙ} {A : Set ℓ} where
  */pt : ϕ ⊢ ⌈ ϕ * A ⌉
  */pt = λ {(ϕ = ⊤) → tt}

  postulate
    */ret : A → ⌈ ϕ * A ⌉

  module _ (B : ⌈ ϕ * A ⌉ → Set ℓ′) (u : ϕ ⊩ λ z → B (*/pt z)) (v : (x : A) → B (*/ret x) [ ϕ ⊢ (λ {(ϕ = ⊤) → u ⋆}) ]) where
    postulate
      */ind : (x : ⌈ ϕ * A ⌉) → B x [ ϕ ⊢ (λ {(ϕ = ⊤) → u ⋆}) ]
      */ind/β : (x : A) → ⌈ */ind (*/ret x) ⌉ ≡ ⌈ v x ⌉
      {-# REWRITE */ind/β #-}

module conn-sub (A : Set) (ϕ : ℙ) (a : ϕ ⊢ A) where
  private
    D : desc lzero ϕ
    D =
      mk-desc (wrap (A [ ϕ ⊢ a ])) λ where
      (ϕ = ⊤) →
        Unit ,
        mk-iso
          (λ _ → mk-wrap ⌊ a ⋆ ⌋)
          (λ _ → tt)
          (λ _ → refl)
          (λ _ → refl)

  open Realign ϕ D public

_[_⊢_]* = conn-sub.tp

conn-sub-syntax = conn-sub.tp
syntax conn-sub-syntax A ϕ (λ z → a) = A [ z ∶ ϕ ⊢ a ]*
