{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check --postfix-projections #-}

module Example where

open import Prelude
open import Closed
open import Gluing

record THEORY ℓ : Set (lsuc ℓ) where
  field
    tp : Set ℓ
    tm : tp → Set ℓ
    prod : tp → tp → tp
    prod/tm : ∀ A B → tm (prod A B) ≅ (tm A × tm B)

open THEORY


module _ (¶ : ℙ) where

  ● : ∀ {ℓ} → Set ℓ → Set ℓ
  ● A = ¶ * A

  postulate 𝓜 : ¶ ⊢ THEORY lzero

  {-# NO_UNIVERSE_CHECK #-}
  record ⟨tp*⟩ : Set (lsuc lzero) where
    constructor mk-tp*-data
    field
      syn : ¶ ⊩ λ z → 𝓜 z .tp
      ext : Set lzero [ z ∶ ¶ ⊢ tm (𝓜 z) (syn z) ]

  open ⟨tp*⟩

  tp*/desc : desc _ ¶
  desc.base tp*/desc = ⟨tp*⟩
  desc.part tp*/desc =
    λ where
    (¶ = ⊤) →
      𝓜 _ .tp ,
      mk-iso
        (λ A → mk-tp*-data (λ _ → A) ⌊ 𝓜 ⋆ .tm A ⌋)
        (λ A → syn A _)
        (λ A → refl)
        (λ A → refl)

  open THEORY


  [tp*] : isom (desc.base tp*/desc)
  [tp*] = ⌈ realign ¶ tp*/desc ⌉

  tp* = [tp*] .fst
  tp*/iso = [tp*] .snd

  tm* : tp* → Set _
  tm* A* = ⌈ tp*/iso .fwd A* .⟨tp*⟩.ext ⌉

  mk-tp* : (syn : ¶ ⊩ λ z → 𝓜 z .tp) → Set lzero [ z ∶ ¶ ⊢ 𝓜 z .tm (syn z) ] → tp*
  mk-tp* syn ext = tp*/iso .bwd (mk-tp*-data syn ext)

  prod*/desc : (A* B* : tp*) → desc _ ¶
  prod*/desc A* B* =
    mk-desc
      (Σ (tm* A*) λ _ → tm* B*)
      λ where
      (¶ = ⊤) →
        𝓜 _ .tm (𝓜 _ .prod A* B*) ,
        𝓜 _ .prod/tm A* B*

  [prod*] : (A B : tp*) → _
  [prod*] A B = realign ¶ (prod*/desc A B)

  prod* : tp* → tp* → tp*
  prod* A B =
    mk-tp*
     (λ {(¶ = ⊤) → 𝓜 _ .prod A B})
     ⌊ fst ⌈ [prod*] A B ⌉ ⌋

  prod/tm* : (A B : tp*) → tm* (prod* A B) ≅ tm* A × tm* B
  prod/tm* A B = snd ⌈ [prod*] A B ⌉

  𝓜* : THEORY _ [ ¶ ⊢ 𝓜 ]
  𝓜* = ⌊ M ⌋
    where
      M : THEORY _
      M .tp = tp*
      M .tm = tm*
      M .prod = prod*
      M .prod/tm = prod/tm*
