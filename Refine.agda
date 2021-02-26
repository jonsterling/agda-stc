{-# OPTIONS --type-in-type --cubical --rewriting --postfix-projections --with-K #-}

module Refine where

open import Prelude
open import Closed
open import Gluing

module _ (ϕ : ℙ) (A : ϕ ⊢ Set) (B : (ϕ ⊩ A) → Set\ ϕ lzero) where
  [refine] : _
  [refine] =
    realign ϕ
      (mk-desc
       (Σ (wrap (ϕ ⊩ A)) λ x → ⌈ B (unwrap x) ⌉)
       λ where
       (ϕ = ⊤) →
         A ⋆ ,
         mk-iso
           (λ x → (mk-wrap (λ _ → x)) , tt)
           (λ x → x .fst .unwrap ⋆)
           (λ x → refl)
           λ x → refl)


  refine : Set
  refine = fst ⌈ [refine] ⌉

⟨_◁_⟩ : ∀ {ϕ} {A} {B : ϕ ⊩ A → Set\ ϕ lzero} → (x : ϕ ⊩ A) → ⌈ B x ⌉ → refine ϕ A B
⟨ x ◁ y ⟩ = ⌈ [refine] _ _ _ ⌉ .snd .bwd (mk-wrap x , y)

unrefine : ∀ {ϕ} {A} {B : ϕ ⊩ A → Set\ ϕ lzero} → refine ϕ A B → ϕ ⊩ A
unrefine x = ⌈ [refine] _ _ _ ⌉ .snd .fwd x .fst .unwrap

refinement : ∀ {ϕ} {A} {B : ϕ ⊩ A → Set\ ϕ lzero} (x : refine ϕ A B) → ⌈ B (unrefine x) ⌉
refinement x = ⌈ [refine] _ _ _ ⌉ .snd .fwd x .snd
