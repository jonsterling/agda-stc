{-# OPTIONS --type-in-type --cubical --rewriting --postfix-projections --with-K #-}

module Example where

open import Prelude
open import Closed
open import Gluing
open import Refine

record THEORY ℓ : Set (lsuc ℓ) where
  field
    tp : Set ℓ
    tm : tp → Set ℓ
    prod : tp → tp → tp
    prod/tm : ∀ A B → tm (prod A B) ≅ (tm A × tm B)
    ans : tp
    yes no : tm ans
    case : ∀ C → tm ans → tm C → tm C → tm C
    case/yes : ∀ C (y n : tm C) → case C yes y n ≡ y
    case/no : ∀ C (y n : tm C) → case C no y n ≡ n

open THEORY


module _ (¶ : ℙ) where

  ● : ∀ {ℓ} → Set ℓ → Set ℓ
  ● A = ⌈ ¶ * A ⌉

  postulate 𝓜 : ¶ ⊢ THEORY lzero

  𝓜/case/yes : z ∶ ¶ ⊩ ∀ C (y n : 𝓜 z .tm C) → 𝓜 z .case C (𝓜 z .yes) y n ≡ y
  𝓜/case/yes z = 𝓜 z .case/yes

  𝓜/case/no : z ∶ ¶ ⊩ ∀ C (y n : 𝓜 z .tm C) → 𝓜 z .case C (𝓜 z .no) y n ≡ n
  𝓜/case/no z = 𝓜 z .case/no

  {-# REWRITE 𝓜/case/yes 𝓜/case/no #-}

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
            (λ A → syn A _)
            (λ A → refl)
            (λ A → refl)

    open Realign ¶ tp*/desc public

  tm* : tp*.tp → Set _
  tm* A = ⌈ tp*.elim A .⟨tp*⟩.ext ⌉

  mk-tp* : (syn : ¶ ⊩ λ z → 𝓜 z .tp) → Set lzero [ z ∶ ¶ ⊢ 𝓜 z .tm (syn z) ] → tp*.tp
  mk-tp* syn ext = tp*.intro (mk-tp*-data syn ext)

  module [prod*] (A B : tp*.tp) where
    private
      D : desc _ ¶
      desc.base D = Σ (tm* A) λ _ → tm* B
      desc.part D =
        λ where
        (¶ = ⊤) →
          𝓜 _ .tm (𝓜 _ .prod A B) ,
          𝓜 _ .prod/tm A B
    open Realign ¶ D public

  prod* : tp*.tp → tp*.tp → tp*.tp
  prod* A B =
    mk-tp*
     (λ {(¶ = ⊤) → 𝓜 _ .prod A B})
     ⌊ [prod*].tp A B ⌋

  prod/tm* : (A B : tp*.tp) → tm* (prod* A B) ≅ tm* A × tm* B
  prod/tm* A B = [prod*].rules A B

  module [ans*] where
    {-# NO_UNIVERSE_CHECK #-}
    data val' : (z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)) → SSet lzero where
      yes' : val' λ z → 𝓜 z .yes
      no' : val' λ z → 𝓜 z .no

    val : _ → Set
    val = λ a → wrap (val' a)

    pattern yes* = mk-wrap yes'
    pattern no* = mk-wrap no'

    open Refine.Refine ¶ (λ z → 𝓜 z .tm (𝓜 z .ans)) (λ a → ¶ * val a) public

  ans* : tp*.tp
  ans* = mk-tp* (λ z → 𝓜 z .ans) ⌊ [ans*].tp ⌋

  yes* : tm* ans*
  yes* = [ans*].intro (λ z → 𝓜 z .yes) (*/ret [ans*].yes*)

  no* : tm* ans*
  no* = [ans*].intro (λ z → 𝓜 z .no) (*/ret [ans*].no*)

  case* : ∀ C (a : tm* ans*) (y : tm* C) (n : tm* C) → tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C a y n}) ]
  case* C a y n = aux ([ans*].unrefine a) ([ans*].refinement a)
    where
      aux : (syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)) (sem : ● ([ans*].val syn)) → tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C (syn ⋆) y n}) ]
      aux syn sem =
        unwrap ⌈
          */ind
           (λ _ → wrap (tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C (syn ⋆) y n}) ]))
           (λ {(¶ = ⊤) → mk-wrap ⌊ 𝓜 _ .case C (syn _) y n ⌋ })
           (λ where
            [ans*].yes* → ⌊ mk-wrap ⌊ y ⌋ ⌋
            [ans*].no* → ⌊ mk-wrap ⌊ n ⌋ ⌋)
           sem
        ⌉

  subtype-transport : ∀ {ℓ} {A : Set ℓ} {a b : ¶ ⊢ A} (p : z ∶ ¶ ⊩ (a z ≡ b z)) → A [ ¶ ⊢ a ] → A [ ¶ ⊢ b ]
  subtype-transport {ℓ} {A} p h = unwrap (coe (λ x → wrap (A [ ¶ ⊢ unwrap x ])) (⊢-ext p) (mk-wrap h))

  correct-eq : {A : Set} {a b : A} (p : a ≡ b) (q : ¶ ⊢ (a ≡ b)) → (a ≡ b) [ ¶ ⊢ q ]
  correct-eq p q = subtype-transport (λ z → uip p (q z)) ⌊ p ⌋


  𝓜* : THEORY _ [ ¶ ⊢ 𝓜 ]
  𝓜* = ⌊ M ⌋
    where
      M : THEORY _
      M .tp = tp*.tp
      M .tm = tm*
      M .prod = prod*
      M .prod/tm = prod/tm*
      M .ans = ans*
      M .yes = yes*
      M .no = no*
      M .case C a y n = ⌈ case* C a y n ⌉
      M .case/yes C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/yes C y n}) ⌉
      M .case/no C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/no C y n}) ⌉
