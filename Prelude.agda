{-# OPTIONS --cubical --rewriting --confluence-check --with-K #-}

module Prelude where

open import Agda.Primitive public
open import Agda.Builtin.Sigma public
open import Agda.Primitive.Cubical public
  renaming (I to ℙ; i0 to ⊥; i1 to ⊤; IsOne to isTrue; itIsOne to ⋆)
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public

coe : {ℓ ℓ′ : _} {A : Set ℓ} (B : A → Set ℓ′) {a0 a1 : A} (p : a0 ≡ a1) → B a0 → B a1
coe B refl x = x

uip : {ℓ : _} {A : Set ℓ} {a0 a1 : A} (p q : a0 ≡ a1) → p ≡ q
uip refl refl = refl


record Unit {ℓ} : Set ℓ where
  constructor tt

infix 10 _⊢_
infix 10 _⊩_
_⊢_ = Partial
_⊩_ = PartialP

PartialP-syntax = PartialP
syntax PartialP-syntax ϕ (λ z → A) = z ∶ ϕ ⊩ A



open import Agda.Builtin.Cubical.Sub public
  renaming (inc to ⌊_⌋; primSubOut to ⌈_⌉)

infix 4 _[_⊢_]
_[_⊢_] = Sub

Sub-syntax = Sub
syntax Sub-syntax A ϕ (λ z → a) = A [ z ∶ ϕ ⊢ a ]


{-# NO_UNIVERSE_CHECK #-}
record wrap {ℓ} (A : SSet ℓ) : Set ℓ where
  constructor mk-wrap
  field
    unwrap : A

open wrap public



postulate
  ⊢-ext : ∀ {ℓ} {ϕ} {A : Set ℓ} {p0 p1 : ϕ ⊢ A} → (z ∶ ϕ ⊩ (p0 z ≡ p1 z)) → mk-wrap p0 ≡ mk-wrap p1
  ⊩-ext : ∀ {ℓ} {ϕ} {A : ϕ ⊢ Set ℓ} {p0 p1 : ϕ ⊩ A} → (z ∶ ϕ ⊩ _≡_ {A = A z} (p0 z) (p1 z)) → mk-wrap p0 ≡ mk-wrap p1



record iso {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor mk-iso
  field
    fwd : A → B
    bwd : B → A
    fwd-bwd : ∀ x → (fwd (bwd x)) ≡ x
    bwd-fwd : ∀ x → (bwd (fwd x)) ≡ x

infix 10 _≅_
_≅_ = iso

open iso public

isom : ∀ {ℓ} (B : Set ℓ) → Set (lsuc ℓ)
isom {ℓ} B = Σ (Set ℓ) λ A → iso A B


infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ[ _ ∈ A ] B
