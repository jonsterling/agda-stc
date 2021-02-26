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


-- TODO
[conn-sub] : (A : Set) (ϕ : ℙ) (a : ϕ ⊢ A) → _
[conn-sub] A ϕ a = realign ϕ ext-desc
  where
    ext-desc : desc lzero ϕ
    ext-desc =
      mk-desc (wrap (A [ ϕ ⊢ a ])) λ where
      (ϕ = ⊤) →
        Unit ,
        mk-iso
          (λ _ → mk-wrap ⌊ a ⋆ ⌋)
          (λ _ → tt)
          (λ _ → refl)
          (λ _ → refl)

conn-sub : (A : Set) (ϕ : ℙ) (a : ϕ ⊢ A) → Set\ ϕ lzero
conn-sub A ϕ a = ⌊ ⌈ [conn-sub] A ϕ a ⌉ .fst ⌋

_[_⊢_]* = conn-sub

syntax conn-sub A ϕ (λ z → a) = A [ z ∶ ϕ ⊢ a ]*

conn-sub/in : {A : Set} {ϕ : ℙ} {a : ϕ ⊢ A} → A [ ϕ ⊢ a ] → ⌈ A [ ϕ ⊢ a ]* ⌉
conn-sub/in {A} {ϕ} {a} h = ⌈ [conn-sub] A ϕ a ⌉ .snd .bwd (mk-wrap h)

conn-sub/out : {A : Set} {ϕ : ℙ} {a : ϕ ⊢ A} → ⌈ A [ ϕ ⊢ a ]* ⌉ → A [ ϕ ⊢ a ]
conn-sub/out {A} {ϕ} {a} h = ⌈ [conn-sub] A ϕ a ⌉ .snd .fwd h .unwrap
