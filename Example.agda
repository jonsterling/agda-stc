{-# OPTIONS --type-in-type --cubical --rewriting --postfix-projections --with-K #-}

module Example where

open import Prelude
open import Closed
open import Gluing
open import Refine

record connective {ℓ} {tp : Set ℓ} (tm : tp → Set ℓ) (A : Set ℓ) : Set ℓ where
  constructor mk-connective
  field
    code : tp
    dec : tm code ≅ A

record THEORY ℓ : Set (lsuc ℓ) where
  field
    tp : Set ℓ
    tm : tp → Set ℓ
    sg : (A : tp) (B : tm A → tp) → connective tm (Σ[ x ∈ tm A ] tm (B x))
    pi : (A : tp) (B : tm A → tp) → connective tm ((x : tm A) → tm (B x))
    bool : tp
    tt ff : tm bool
    case : ∀ C → tm bool → tm C → tm C → tm C
    case/tt : ∀ C (y n : tm C) → case C tt y n ≡ y
    case/ff : ∀ C (y n : tm C) → case C ff y n ≡ n

open THEORY


module _ (¶ : ℙ) where

  ● : ∀ {ℓ} → Set ℓ → Set ℓ
  ● A = ⌈ ¶ * A ⌉

  postulate 𝓜 : ¶ ⊢ THEORY lzero

  𝓜/case/tt : z ∶ ¶ ⊩ ∀ C (y n : 𝓜 z .tm C) → 𝓜 z .case C (𝓜 z .tt) y n ≡ y
  𝓜/case/tt z = 𝓜 z .case/tt

  𝓜/case/ff : z ∶ ¶ ⊩ ∀ C (y n : 𝓜 z .tm C) → 𝓜 z .case C (𝓜 z .ff) y n ≡ n
  𝓜/case/ff z = 𝓜 z .case/ff

  {-# REWRITE 𝓜/case/tt 𝓜/case/ff #-}

  {-# NO_UNIVERSE_CHECK #-}
  record ⟨tp*⟩ : Set (lsuc lzero) where
    constructor mk-tp*-data
    field
      syn : ¶ ⊩ λ z → 𝓜 z .tp
      ext : Set lzero [ z ∶ ¶ ⊢ tm (𝓜 z) (syn z) ]
  open THEORY

  module tp* where
    private
      D : desc _ ¶
      desc.base D = ⟨tp*⟩
      desc.part D =
        λ where
        (¶ = ⊤) →
          𝓜 _ .tp ,
          mk-iso
            (λ A → mk-tp*-data (λ _ → A) ⌊ 𝓜 ⋆ .tm A ⌋)
            (λ A → ⟨tp*⟩.syn A _)
            (λ A → refl)
            (λ A → refl)

    open Realign ¶ D public

  tm* : tp*.tp → Set _
  tm* A = ⌈ tp*.elim A .⟨tp*⟩.ext ⌉

  mk-tp* : (syn : ¶ ⊩ λ z → 𝓜 z .tp) → Set lzero [ z ∶ ¶ ⊢ 𝓜 z .tm (syn z) ] → tp*.tp
  mk-tp* syn ext = tp*.intro (mk-tp*-data syn ext)

  module AlignConnective (E : Set) (syn : z ∶ ¶ ⊩ connective (𝓜 z .tm) E) where
    open connective

    D : desc _ ¶
    desc.base D = E
    desc.part D = λ where (¶ = ⊤) → 𝓜 ⋆ .tm (syn ⋆ .code) , syn ⋆ .dec

    module R = Realign ¶ D

    conn : connective tm* E
    code conn = mk-tp* (λ where (¶ = ⊤) → syn ⋆ .code) ⌊ R.tp ⌋
    dec conn = R.rules

  module sg* (A : tp*.tp) (B : tm* A → tp*.tp) = AlignConnective (Σ[ x ∈ tm* A ] tm* (B x)) (λ where (¶ = ⊤) → 𝓜 ⋆ .sg A B)
  module pi* (A : tp*.tp) (B : tm* A → tp*.tp) = AlignConnective ((x : tm* A) → tm* (B x)) (λ where (¶ = ⊤) → 𝓜 ⋆ .pi A B)

  module [bool*] where
    data val' : (z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .bool)) → SSet lzero where
      tt' : val' λ z → 𝓜 z .tt
      ff' : val' λ z → 𝓜 z .ff

    val : _ → Set
    val = λ a → wrap (val' a)

    pattern tt* = mk-wrap tt'
    pattern ff* = mk-wrap ff'

    open Refine.Refine ¶ (λ z → 𝓜 z .tm (𝓜 z .bool)) (λ a → ¶ * val a) public

  bool* : tp*.tp
  bool* = mk-tp* (λ z → 𝓜 z .bool) ⌊ [bool*].tp ⌋

  tt* : tm* bool*
  tt* = [bool*].intro (λ z → 𝓜 z .tt) (*/ret [bool*].tt*)

  ff* : tm* bool*
  ff* = [bool*].intro (λ z → 𝓜 z .ff) (*/ret [bool*].ff*)

  case* : ∀ C (a : tm* bool*) (y : tm* C) (n : tm* C) → tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C a y n}) ]
  case* C a y n = aux ([bool*].unrefine a) ([bool*].refinement a)
    where
      aux : (syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .bool)) (sem : ● ([bool*].val syn)) → tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C (syn ⋆) y n}) ]
      aux syn sem =
        unwrap ⌈
          */ind
           (λ _ → wrap (tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C (syn ⋆) y n}) ]))
           (λ {(¶ = ⊤) → mk-wrap ⌊ 𝓜 _ .case C (syn _) y n ⌋ })
           (λ where
            [bool*].tt* → ⌊ mk-wrap ⌊ y ⌋ ⌋
            [bool*].ff* → ⌊ mk-wrap ⌊ n ⌋ ⌋)
           sem
        ⌉

  subtype-trboolport : ∀ {ℓ} {A : Set ℓ} {a b : ¶ ⊢ A} (p : z ∶ ¶ ⊩ (a z ≡ b z)) → A [ ¶ ⊢ a ] → A [ ¶ ⊢ b ]
  subtype-trboolport {ℓ} {A} p h = unwrap (coe (λ x → wrap (A [ ¶ ⊢ unwrap x ])) (⊢-ext p) (mk-wrap h))

  correct-eq : {A : Set} {a b : A} (p : a ≡ b) (q : ¶ ⊢ (a ≡ b)) → (a ≡ b) [ ¶ ⊢ q ]
  correct-eq p q = subtype-trboolport (λ z → uip p (q z)) ⌊ p ⌋


  𝓜* : THEORY _ [ ¶ ⊢ 𝓜 ]
  𝓜* = ⌊ M ⌋
    where
      M : THEORY _
      M .tp = tp*.tp
      M .tm = tm*
      M .sg = sg*.conn
      M .pi = pi*.conn
      M .bool = bool*
      M .tt = tt*
      M .ff = ff*
      M .case C a y n = ⌈ case* C a y n ⌉
      M .case/tt C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/tt C y n}) ⌉
      M .case/ff C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/ff C y n}) ⌉
