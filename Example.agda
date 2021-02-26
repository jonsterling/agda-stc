{-# OPTIONS --type-in-type --cubical --rewriting --postfix-projections #-}

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
    ans : tp
    yes no : tm ans

open THEORY


module _ (¶ : ℙ) where

  ● : ∀ {ℓ} → Set ℓ → Set ℓ
  ● A = ⌈ ¶ * A ⌉

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


  {-# NO_UNIVERSE_CHECK #-}
  data ⟨ans*⟩∋_ : (z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)) → Set lzero where
    ⟨yes*⟩ : ⟨ans*⟩∋ λ z → 𝓜 z .yes
    ⟨no*⟩ : ⟨ans*⟩∋ λ z → 𝓜 z .no

  {-# NO_UNIVERSE_CHECK #-}
  record ⟨ans*⟩ : Set lzero where
    constructor mk-⟨ans*⟩
    field
      syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)
      sem : ● (⟨ans*⟩∋ syn)

  ans*/desc : desc _ ¶
  ans*/desc =
    mk-desc ⟨ans*⟩ λ where
    (¶ = ⊤) →
      (𝓜 ⋆ .tm (𝓜 ⋆ .ans)) ,
      mk-iso
        (λ x → mk-⟨ans*⟩ (λ _ → x) tt)
        (λ x → ⟨ans*⟩.syn x ⋆)
        (λ x → refl)
        (λ x → refl)

  [ans*] : _
  [ans*] = realign ¶ ans*/desc

  ans* : tp*
  ans* = mk-tp* (λ z → 𝓜 z .ans) ⌊ ⌈ [ans*] ⌉ .fst ⌋

  mk-ans* : (syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)) → ● (⟨ans*⟩∋ syn) → tm* ans*
  mk-ans* syn sem = ⌈ [ans*] ⌉ .snd .bwd (mk-⟨ans*⟩ syn sem)

  yes* : tm* ans*
  yes* = mk-ans* _ (*/ret ⟨yes*⟩)

  no* : tm* ans*
  no* = mk-ans* _ (*/ret ⟨no*⟩)

  𝓜* : THEORY _ [ ¶ ⊢ 𝓜 ]
  𝓜* = ⌊ M ⌋
    where
      M : THEORY _
      M .tp = tp*
      M .tm = tm*
      M .prod = prod*
      M .prod/tm = prod/tm*
      M .ans = ans*
      M .yes = yes*
      M .no = no*
