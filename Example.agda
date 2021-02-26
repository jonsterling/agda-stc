{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check #-}

module Example where
open import Prelude
open import Closed
open import Gluing

record THEORY ℓ : Type (ℓ-suc ℓ) where
  field
    tp : Type ℓ
    tm : tp → Type ℓ
    prod : tp → tp → tp
    prod/tm : ∀ A B → iso {ℓ} (tm (prod A B)) (Σ (tm A) (λ _ → tm B))
open THEORY


module _ (¶ : I) where

  ○ : ∀ {ℓ} → Type ℓ → SSet ℓ
  ○ A = .(_ : IsOne ¶) → A

  ● : ∀ {ℓ} → Type ℓ → Type ℓ
  ● A = ¶ * A

  [○] : ∀ {ℓ} → ○ (Type ℓ) → SSet ℓ
  [○] A = PartialP ¶ A


  module _ .(_ : IsOne ¶) where
    postulate
      M : THEORY ℓ-zero


  {-# NO_UNIVERSE_CHECK #-}
  record tp*-data : Type (ℓ-suc ℓ-zero) where
    constructor mk-tp*-data
    field
      syn : [○] (λ z → tp (M z))
      ext : Type ℓ-zero [ ¶ ↦ (λ z → tm (M z) (syn z)) ]

  open tp*-data

  tp*/desc : desc (ℓ-suc ℓ-zero) ¶
  desc.base tp*/desc = tp*-data
  desc.part tp*/desc =
    λ where
    (¶ = i1) →
      tp (M _) ,
      mk-iso
        (λ A → mk-tp*-data (λ _ → A) (inS (tm (M 1=1) A)))
        (λ A → syn A _)
        (λ A → _≣_.refl)
        (λ A → _≣_.refl)

  open THEORY


  [tp*] : isom (desc.base tp*/desc) [ ¶ ↦ desc.part tp*/desc ]
  [tp*] = realign ¶ tp*/desc

  tp* : Type (ℓ-suc ℓ-zero)
  tp* = fst (outS [tp*])

  tm* : tp* → Type _
  tm* A* = outS (tp*-data.ext (iso.fwd (snd (outS [tp*])) A*))

  mk-tp* = iso.bwd (snd (outS [tp*]))

  prod*/desc : (A* B* : tp*) → desc ℓ-zero ¶
  prod*/desc A* B* =
    mk-desc
      (Σ (tm* A*) λ _ → tm* B*)
      λ where
      (¶ = i1) →
        tm (M _) (prod (M _) A* B*) ,
        prod/tm (M _) A* B*

  [prod*] : (A B : tp*) → isom (desc.base (prod*/desc A B)) [ ¶ ↦ desc.part (prod*/desc A B) ]
  [prod*] A B = realign ¶ (prod*/desc A B)

  prod* : tp* → tp* → tp*
  prod* A B =
    mk-tp*
    (mk-tp*-data
     (λ {(¶ = i1)→ prod (M _) A B})
     (inS (fst (outS ([prod*] A B)))))

  prod/tm* : (A B : tp*) → iso (tm* (prod* A B)) (Σ (tm* A) (λ _ → tm* B))
  prod/tm* A B = snd (outS ([prod*] A B))

  M* : THEORY (ℓ-suc ℓ-zero) [ ¶ ↦ M ]
  M* =
   inS record
    { tp = tp* ;
      tm = tm* ;
      prod = prod* ;
      prod/tm = prod/tm* }
