{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check #-}

module Example where
open import Prelude
open import Closed
open import Gluing

record THEORY ℓ : Set (lsuc ℓ) where
  field
    tp : Set ℓ
    tm : tp → Set ℓ
    prod : tp → tp → tp
    prod/tm : ∀ A B → iso {ℓ} (tm (prod A B)) (Σ (tm A) (λ _ → tm B))

open THEORY


module _ (¶ : ℙ) where

  ● : ∀ {ℓ} → Set ℓ → Set ℓ
  ● A = ¶ * A

  module _ .(_ : IsOne ¶) where
    postulate
      M : THEORY lzero


  {-# NO_UNIVERSE_CHECK #-}
  record tp*-data : Set (lsuc lzero) where
    constructor mk-tp*-data
    field
      syn : ¶ ⊩ λ z → tp (M z)
      ext : Set lzero [ ¶ ↦ (λ z → tm (M z) (syn z)) ]

  open tp*-data

  tp*/desc : desc _ ¶
  desc.base tp*/desc = tp*-data
  desc.part tp*/desc =
    λ where
    (¶ = ⊤) →
      tp (M _) ,
      mk-iso
        (λ A → mk-tp*-data (λ _ → A) ⌊ (tm (M ⋆) A) ⌋)
        (λ A → syn A _)
        (λ A → refl)
        (λ A → refl)

  open THEORY


  [tp*] : isom (desc.base tp*/desc) [ ¶ ↦ desc.part tp*/desc ]
  [tp*] = realign ¶ tp*/desc

  tp* : Set _
  tp* = fst ⌈ [tp*] ⌉

  tm* : tp* → Set _
  tm* A* = ⌈ tp*-data.ext (iso.fwd (snd ⌈ [tp*] ⌉) A*) ⌉

  mk-tp* = iso.bwd (snd ⌈ [tp*] ⌉)

  prod*/desc : (A* B* : tp*) → desc _ ¶
  prod*/desc A* B* =
    mk-desc
      (Σ (tm* A*) λ _ → tm* B*)
      λ where
      (¶ = ⊤) →
        tm (M _) (prod (M _) A* B*) ,
        prod/tm (M _) A* B*

  [prod*] : (A B : tp*) → isom (desc.base (prod*/desc A B)) [ ¶ ↦ desc.part (prod*/desc A B) ]
  [prod*] A B = realign ¶ (prod*/desc A B)

  prod* : tp* → tp* → tp*
  prod* A B =
    mk-tp*
    (mk-tp*-data
     (λ {(¶ = ⊤)→ prod (M _) A B})
     ⌊ (fst (⌈ [prod*] A B ⌉)) ⌋)

  prod/tm* : (A B : tp*) → iso (tm* (prod* A B)) (Σ (tm* A) (λ _ → tm* B))
  prod/tm* A B = snd ⌈ [prod*] A B ⌉

  M* : THEORY _ [ ¶ ↦ M ]
  M* =
   ⌊ record
    { tp = tp* ;
      tm = tm* ;
      prod = prod* ;
      prod/tm = prod/tm* }
   ⌋
