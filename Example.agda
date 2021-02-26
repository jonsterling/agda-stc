{-# OPTIONS --type-in-type --cubical --rewriting --postfix-projections --with-K #-}

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
  data ⟨ans*⟩∋_ : (z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)) → SSet lzero where
    ⟨yes*⟩ : ⟨ans*⟩∋ λ z → 𝓜 z .yes
    ⟨no*⟩ : ⟨ans*⟩∋ λ z → 𝓜 z .no

  {-# NO_UNIVERSE_CHECK #-}
  record ⟨ans*⟩ : Set lzero where
    constructor mk-⟨ans*⟩
    field
      syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)
      sem : ● (wrap (⟨ans*⟩∋ syn))

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

  mk-ans* : (syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .ans)) → ● (wrap (⟨ans*⟩∋ syn)) → tm* ans*
  mk-ans* syn sem = ⌈ [ans*] ⌉ .snd .bwd (mk-⟨ans*⟩ syn sem)

  yes* : tm* ans*
  yes* = mk-ans* _ (*/ret (mk-wrap ⟨yes*⟩))

  no* : tm* ans*
  no* = mk-ans* _ (*/ret (mk-wrap ⟨no*⟩))

  case*' : ∀ C (a : ⟨ans*⟩) (y : tm* C) (n : tm* C) → tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C (⌈ [ans*] ⌉ .snd .bwd a) y n}) ]
  case*' C (mk-⟨ans*⟩ syn sem) y n =
    unwrap ⌈
      */ind
       (λ _ → wrap (tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C (syn ⋆) y n}) ]))
       (λ {(¶ = ⊤) → mk-wrap ⌊ (𝓜 _ .case C (syn _) y n) ⌋ })
       (λ where
        (mk-wrap ⟨yes*⟩) → ⌊ mk-wrap ⌊ y ⌋ ⌋
        (mk-wrap ⟨no*⟩) → ⌊ mk-wrap ⌊ n ⌋ ⌋)
       sem
    ⌉

  case* : ∀ C (a : tm* ans*) (y : tm* C) (n : tm* C) → tm* C [ ¶ ⊢ (λ {(¶ = ⊤) → 𝓜 ⋆ .case C a y n}) ]
  case* C a y n = case*' C (⌈ [ans*] ⌉ .snd .fwd a) y n

  subtype-transport : ∀ {ℓ} {A : Set ℓ} {a b : ¶ ⊢ A} (p : z ∶ ¶ ⊩ (a z ≡ b z)) → A [ ¶ ⊢ a ] → A [ ¶ ⊢ b ]
  subtype-transport {ℓ} {A} p h = unwrap (coe (λ x → wrap (A [ ¶ ⊢ unwrap x ])) (⊢-ext p) (mk-wrap h))

  correct-eq : {A : Set} {a b : A} (p : a ≡ b) (q : ¶ ⊢ (a ≡ b)) → (a ≡ b) [ ¶ ⊢ q ]
  correct-eq p q = subtype-transport (λ z → uip p (q z)) ⌊ p ⌋

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
      M .case C a y n = ⌈ case* C a y n ⌉
      M .case/yes C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/yes C y n}) ⌉
      M .case/no C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/no C y n}) ⌉
