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
  */pt = λ {(ϕ = ⊤) → <>}

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
          (λ _ → <>)
          (λ _ → refl)
          (λ _ → refl)

  module R = Realign ϕ D
  open R hiding (elim; intro) public

  elim : tp → A [ ϕ ⊢ a ]
  elim x = unwrap (R.elim x)

  intro : A [ ϕ ⊢ a ] → tp
  intro x = R.intro (mk-wrap x)

_[_⊢_]* : (A : Set) (ϕ : ℙ) (a : ϕ ⊢ A) → Set\ ϕ lzero
A [ ϕ ⊢ a ]* = ⌊ conn-sub.tp A ϕ a ⌋

conn-sub-syntax = _[_⊢_]*
syntax conn-sub-syntax A ϕ (λ z → a) = A [ z ∶ ϕ ⊢ a ]*
