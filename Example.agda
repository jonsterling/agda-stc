{-# OPTIONS --cubical --rewriting --postfix-projections --with-K #-}

module Example where

open import Prelude
open import Closed
open import Gluing
open import Refine

record connective {ℓ ℓ′} {tp : Set ℓ} (tm : tp → Set ℓ′) (A : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor mk-connective
  field
    code : tp
    dec : tm code ≅ A

open connective

record 𝕋 ℓ ℓ′ : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    tp : Set ℓ
    tm : tp → Set ℓ′
    sg : (A : tp) (B : tm A → tp) → connective tm (Σ[ x ∈ tm A ] tm (B x))
    pi : (A : tp) (B : tm A → tp) → connective tm ((x : tm A) → tm (B x))
    bool : tp
    tt ff : tm bool
    case : ∀ C → tm bool → tm C → tm C → tm C
    case/tt : ∀ C (y n : tm C) → case C tt y n ≡ y
    case/ff : ∀ C (y n : tm C) → case C ff y n ≡ n

open 𝕋



module _ (¶ : ℙ) where

  ● : ∀ {ℓ} → Set ℓ → Set ℓ
  ● A = ⌈ ¶ * A ⌉

  postulate 𝓜 : ¶ ⊢ 𝕋 (lsuc lzero) lzero

  𝓜/case/tt : z ∶ ¶ ⊩ ∀ C (y n : 𝓜 z .tm C) → 𝓜 z .case C (𝓜 z .tt) y n ≡ y
  𝓜/case/tt z = 𝓜 z .case/tt

  𝓜/case/ff : z ∶ ¶ ⊩ ∀ C (y n : 𝓜 z .tm C) → 𝓜 z .case C (𝓜 z .ff) y n ≡ n
  𝓜/case/ff z = 𝓜 z .case/ff

  {-# REWRITE 𝓜/case/tt 𝓜/case/ff #-}

  _→vert_ : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ [ _ ∶ ¶ ⊢ A ]) → SSet ℓ
  A →vert B = (x : A) → ⌈ B ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → x ) ]

  postulate
    var : (A : z ∶ ¶ ⊩ 𝓜 z .tp) → Set [ z ∶ ¶ ⊢ 𝓜 z .tm (A z) ]
    ne : (A : z ∶ ¶ ⊩ 𝓜 z .tp) → Set [ z ∶ ¶ ⊢ 𝓜 z .tm (A z) ]
    nf : (A : z ∶ ¶ ⊩ 𝓜 z .tp) → Set [ z ∶ ¶ ⊢ 𝓜 z .tm (A z) ]
    nftp : Set (lsuc lzero) [ z ∶ ¶ ⊢ 𝓜 z .tp ]
    𝔳𝔞𝔯 : {A : z ∶ ¶ ⊩ 𝓜 z .tp} (x : ⌈ var A ⌉) → ⌈ ne A ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → x) ]
    𝔭𝔦 : (𝔄 : ⌈ nftp ⌉) (𝔅 : ⌈ var (λ where (¶ = ⊤) → 𝔄) ⌉ → ⌈ nftp ⌉) → ⌈ nftp ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .pi 𝔄 𝔅 .code) ]
    𝔰𝔤 : (𝔄 : ⌈ nftp ⌉) (𝔅 : ⌈ var (λ where (¶ = ⊤) → 𝔄) ⌉ → ⌈ nftp ⌉) → ⌈ nftp ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .sg 𝔄 𝔅 .code) ]
    𝔟𝔬𝔬𝔩 : ⌈ nftp ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .bool) ]
    𝔱𝔱 : ⌈ nf (λ z → 𝓜 z .bool) ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .tt) ]
    𝔣𝔣 : ⌈ nf (λ z → 𝓜 z .bool) ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .ff) ]
    𝔩𝔦𝔣𝔱 : ⌈ ne (λ z → 𝓜 z .bool) ⌉ →vert nf λ z → 𝓜 z .bool

    𝔣𝔰𝔱 : {A : z ∶ ¶ ⊩ 𝓜 z .tp} {B : z ∶ ¶ ⊩ (𝓜 z .tm (A z) → 𝓜 z .tp)} (𝔢 : ⌈ ne (λ z → 𝓜 z .sg (A z) (B z) .code) ⌉) → ⌈ ne A ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .sg (A ⋆) (B ⋆) .dec .fwd 𝔢 .fst ) ]
    𝔰𝔫𝔡 : {A : z ∶ ¶ ⊩ 𝓜 z .tp} {B : z ∶ ¶ ⊩ (𝓜 z .tm (A z) → 𝓜 z .tp)} (𝔢 : ⌈ ne (λ z → 𝓜 z .sg (A z) (B z) .code) ⌉) → ⌈ ne (λ where (¶ = ⊤) → B ⋆ (𝓜 ⋆ .sg (A ⋆) (B ⋆) .dec .fwd 𝔢 .fst)) ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .sg (A ⋆) (B ⋆) .dec .fwd 𝔢 .snd ) ]
    𝔠𝔞𝔰𝔢 : (ℭ : ⌈ nftp ⌉) (𝔟 : ⌈ ne (λ z → 𝓜 z .bool) ⌉) (𝔱 : ⌈ nf (λ where (¶ = ⊤) → ℭ) ⌉) (𝔣 : ⌈ nf (λ where (¶ = ⊤) → ℭ) ⌉) → ⌈ ne (λ where (¶ = ⊤) → ℭ) ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → 𝓜 ⋆ .case ℭ 𝔟 𝔱 𝔣) ]


  {-# NO_UNIVERSE_CHECK #-}
  record ⟨tp*⟩ : Set (lsuc lzero) where
    constructor mk-tp*-data
    field
      syn : ¶ ⊩ λ z → 𝓜 z .tp
      norm : ⌈ nftp ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → syn ⋆) ]
      ext : Set lzero [ z ∶ ¶ ⊢ tm (𝓜 z) (syn z) ]
      reflect : ⌈ ne syn ⌉ →vert ext
      reify : ⌈ ext ⌉ →vert nf syn

  module tp* where
    private
      D : desc (lsuc lzero) ¶
      desc.base D = ⟨tp*⟩
      desc.part D =
        λ where
        (¶ = ⊤) →
          𝓜 ⋆ .tp ,
          mk-iso
            (λ A → mk-tp*-data (λ _ → A) ⌊ A ⌋ ⌊ 𝓜 ⋆ .tm A ⌋ (λ x → ⌊ x ⌋) λ x → ⌊ x ⌋)
            (λ A → ⟨tp*⟩.syn A _)
            (λ A → refl)
            (λ A → refl)

    open Realign ¶ D public

  tm* : tp*.tp → Set _
  tm* A = ⌈ tp*.elim A .⟨tp*⟩.ext ⌉

  ⇓ : (A : tp*.tp) → ⌈ nftp ⌉
  ⇓ A = ⌈ tp*.elim A .⟨tp*⟩.norm ⌉

  ↑[_] : (A : tp*.tp) → ⌈ ne (λ where (¶ = ⊤) → A) ⌉ → tm* A
  ↑[ A ] a = ⌈ tp*.elim A .⟨tp*⟩.reflect a ⌉

  ↓[_] : (A : tp*.tp) → tm* A → ⌈ nf (λ where (¶ = ⊤) → A) ⌉
  ↓[ A ] a = ⌈ tp*.elim A .⟨tp*⟩.reify a ⌉

  module AlignConnective
    (E : Set)
    (syn : z ∶ ¶ ⊩ connective (𝓜 z .tm) E)
    (norm : ⌈ nftp ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → syn ⋆ .code) ])
    where
    open connective

    D : desc _ ¶
    desc.base D = E
    desc.part D = λ where (¶ = ⊤) → 𝓜 ⋆ .tm (syn ⋆ .code) , syn ⋆ .dec

    module R = Realign ¶ D

    module _ (reflect : ⌈ ne (λ z → syn z .code) ⌉ →vert ⌊ R.tp ⌋) (reify : R.tp →vert nf (λ z → syn z .code)) where
      conn : connective tm* E
      code conn = tp*.intro (mk-tp*-data (λ where (¶ = ⊤) → syn ⋆ .code) norm ⌊ R.tp ⌋ reflect reify)
      dec conn = R.rules

  module sg* (A : tp*.tp) (B : tm* A → tp*.tp) where
    module Align =
      AlignConnective
       (Σ[ x ∈ tm* A ] tm* (B x))
       (λ where (¶ = ⊤) → 𝓜 ⋆ .sg A B)
       (𝔰𝔤 (⇓ A) (λ x → ⇓ (B (↑[ A ] ⌈ 𝔳𝔞𝔯 x ⌉))))

    open Align hiding (conn) public

    reflect : ⌈ ne (λ { (¶ = ⊤) → 𝓜 ⋆ .sg A B .code }) ⌉ →vert ⌊ R.tp ⌋
    reflect x =
      let x0 = ↑[ A ] ⌈ 𝔣𝔰𝔱 {λ where (¶ = ⊤) → A} {λ where (¶ = ⊤) → B} x ⌉ in
      let x1 = ↑[ B x0 ] ⌈ 𝔰𝔫𝔡 {λ where (¶ = ⊤) → A} {λ where (¶ = ⊤) → B} x ⌉ in
      let asdfasdf = R.intro (x0 , x1) in
      let asdfa = ⌈ R.realign ⌉ .snd .bwd (x0 , x1) in
      ⌊ asdfa ⌋

    reify : Align.R.tp →vert nf (λ { (¶ = ⊤) → 𝓜 ⋆ .sg A B .code })
    reify = {!!}

    conn = Align.conn reflect reify


  module pi* (A : tp*.tp) (B : tm* A → tp*.tp) =
    AlignConnective
      ((x : tm* A) → tm* (B x))
      (λ where (¶ = ⊤) → 𝓜 ⋆ .pi A B)
      (𝔭𝔦 (⇓ A) (λ x → ⇓ (B (↑[ A ] ⌈ 𝔳𝔞𝔯 x ⌉))))

  module [bool*] where
    data val' : (z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .bool)) → SSet lzero where
      ne' : (x : ⌈ ne (λ z → 𝓜 z .bool) ⌉) → val' λ where (¶ = ⊤) → x
      tt' : val' λ z → 𝓜 z .tt
      ff' : val' λ z → 𝓜 z .ff

    val : _ → Set
    val = λ a → wrap (val' a)

    pattern tt* = mk-wrap tt'
    pattern ff* = mk-wrap ff'
    pattern ne* e = mk-wrap (ne' e)

    module R = Refine.Refine ¶ (λ z → 𝓜 z .tm (𝓜 z .bool)) (λ a → ¶ * val a)

    reflect : ⌈ ne (λ z → 𝓜 z .bool) ⌉ →vert ⌊ R.tp ⌋
    reflect x = ⌊ R.intro (λ where (¶ = ⊤) → x) (*/ret (mk-wrap (ne' x))) ⌋

    reify : R.tp →vert nf (λ z → 𝓜 z .bool)
    reify = λ x → aux (R.unrefine x) (R.refinement x)
      where
        aux : (syn : z ∶ ¶ ⊩ 𝓜 z .tm (𝓜 z .bool)) (sem : ● (val syn)) → ⌈ nf (λ z → 𝓜 z .bool) ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → syn ⋆) ]
        aux syn sem =
          unwrap ⌈
            */ind
              (λ _ → wrap (⌈ nf (λ z → 𝓜 z .bool) ⌉ [ ¶ ⊢ (λ where (¶ = ⊤) → syn ⋆) ]))
              (λ where (¶ = ⊤) → mk-wrap ⌊ syn ⋆ ⌋)
              (λ where
               tt* → ⌊ mk-wrap 𝔱𝔱 ⌋
               ff* → ⌊ mk-wrap 𝔣𝔣 ⌋
               (ne* x) → ⌊ mk-wrap (𝔩𝔦𝔣𝔱 x) ⌋)
              sem
          ⌉

    open R public


  bool* : tp*.tp
  bool* = tp*.intro (mk-tp*-data (λ z → 𝓜 z .bool) 𝔟𝔬𝔬𝔩 ⌊ [bool*].tp ⌋ [bool*].reflect [bool*].reify)

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
            [bool*].ff* → ⌊ mk-wrap ⌊ n ⌋ ⌋
            ([bool*].ne* x) → ⌊ mk-wrap ⌊ ↑[ C ] ⌈ 𝔠𝔞𝔰𝔢 (⇓ C) x (↓[ C ] y) (↓[ C ] n) ⌉ ⌋ ⌋)
           sem
        ⌉

  replace-boundary : ∀ {ℓ} {A : Set ℓ} {a b : ¶ ⊢ A} (p : z ∶ ¶ ⊩ (a z ≡ b z)) → A [ ¶ ⊢ a ] → A [ ¶ ⊢ b ]
  replace-boundary {ℓ} {A} p h = unwrap (coe (λ x → wrap (A [ ¶ ⊢ unwrap x ])) (⊢-ext p) (mk-wrap h))

  correct-eq : {A : Set} {a b : A} (p : a ≡ b) (q : ¶ ⊢ (a ≡ b)) → (a ≡ b) [ ¶ ⊢ q ]
  correct-eq p q = replace-boundary (λ z → uip p (q z)) ⌊ p ⌋

  𝓜* : 𝕋 _ _ [ ¶ ⊢ 𝓜 ]
  𝓜* = ⌊ M ⌋
    where
      M : 𝕋 _ _
      M .tp = tp*.tp
      M .tm = tm*
      M .sg A B = {!!}
      M .pi = {!!} -- pi*.conn ? ?
      M .bool = bool*
      M .tt = tt*
      M .ff = ff*
      M .case C a y n = ⌈ case* C a y n ⌉
      M .case/tt C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/tt C y n}) ⌉
      M .case/ff C y n = ⌈ correct-eq refl (λ {(¶ = ⊤) → 𝓜 ⋆ .case/ff C y n}) ⌉

    {-



-}
