{-# OPTIONS --type-in-type --cubical --rewriting --confluence-check #-}

module stc-playground where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.Equality renaming (_≡_ to _≣_)
open import Agda.Builtin.Equality.Rewrite
open import Agda.Primitive


module _ {ℓ} where
  postulate
    _*_ : ∀ (ϕ : I) (A : Type ℓ) → Type ℓ

  module _ {ϕ : I} {A : Type ℓ} where
    postulate
      */pt : Partial ϕ (ϕ * A)
      [*/ret] : A → ϕ * A [ ϕ ↦ */pt ]

    */ret : A → ϕ * A
    */ret a = outS ([*/ret] a)

    postulate
      */glue
        : (B : _*_ ϕ A → Type ℓ)
        → (u : PartialP ϕ (λ z → B (*/pt z)))
        → (v : (x : A) → B (*/ret x) [ ϕ ↦ (λ {(ϕ = i1) → u _}) ])
        → (x : ϕ * A)
        → B x

      */glue/β
        : (B : _*_ ϕ A → Type ℓ)
        → (u : PartialP ϕ (λ z → B (*/pt z)))
        → (v : (x : A) → B (*/ret x) [ ϕ ↦ (λ {(ϕ = i1) → u _}) ])
        → (x : A)
        → */glue B u v (*/ret x) ≣ outS (v x)
      {-# REWRITE */glue/β #-}


record iso {ℓ} (A B : Type ℓ) : Type ℓ where
  constructor mk-iso
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → (fwd (bwd x)) ≣ x
    bwd-fwd : ∀ x → (bwd (fwd x)) ≣ x

isom : ∀ {ℓ} (B : Type ℓ) → Type (ℓ-suc ℓ)
isom {ℓ} B = Σ (Type ℓ) λ A → iso A B

{-# NO_UNIVERSE_CHECK #-}
record desc ℓ (ϕ : I) : Type (ℓ-suc ℓ) where
  constructor mk-desc
  field
    base : Type ℓ
    part : Partial ϕ (isom base)

postulate
  realign : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) → isom (desc.base D) [ ϕ ↦ desc.part D ]

  realign/fwd-bwd : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) (x : _) → iso.fwd (snd (outS (realign ϕ D))) (iso.bwd (snd (outS (realign ϕ D))) x) ≣ x
  realign/bwd-fwd : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) (x : fst (outS (realign ϕ D))) → iso.bwd (snd (outS (realign ϕ D))) (iso.fwd (snd (outS (realign ϕ D))) x) ≣ x
  {-# REWRITE realign/fwd-bwd #-}

[realign/tp] : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) → Type ℓ [ ϕ ↦ (λ z → fst (desc.part D z)) ]
[realign/tp] ϕ D = inS (fst (outS (realign ϕ D)))

realign/tp : ∀ {ℓ} (ϕ : I) (D : desc ℓ ϕ) → Type ℓ
realign/tp ϕ D = fst (outS (realign ϕ D))


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
