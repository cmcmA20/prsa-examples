{-# OPTIONS --safe #-}
open import Level using (Level; suc; _⊔_; 0ℓ)

module Data.Scoped
  {ℓ : Level}
  (𝐾 : Set ℓ)
  where

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Endofunctor; Functor)
open Functor using (F₀; F₁)
open import Data.Bool using (Bool; false; true)
open import Data.Bwd using (Bwd; []; _-,_; _++_)
  public
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_|>_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Relation.Unary using (Pred; IUniversal; _⇒_)
  public

private variable
  ℓ₁ : Level
  k : 𝐾
  iz iz′ jz jz′ kz kz′ ijz ijz′ : Bwd 𝐾

infixr 19 _⊑_
data _⊑_ : Bwd 𝐾 → Bwd 𝐾 → Set ℓ where
  _o′ : iz ⊑ jz → iz        ⊑ (jz -, k)
  _os : iz ⊑ jz → (iz -, k) ⊑ (jz -, k)
  oz :            []        ⊑ []

_⟵_ : 𝐾 → Bwd 𝐾 → Set ℓ
k ⟵ kz = ([] -, k) ⊑ kz

_++⊑_ : iz ⊑ jz → iz′ ⊑ jz′ → (iz ++ iz′) ⊑ (jz ++ jz′)
θ ++⊑ (ϕ o′) = (θ ++⊑ ϕ) o′
θ ++⊑ (ϕ os) = (θ ++⊑ ϕ) os
θ ++⊑ oz     = θ

oi : kz ⊑ kz
oi {[]     } = oz
oi {kz -, _} = oi os

oe : [] ⊑ kz
oe {[]     } = oz
oe {kz -, k} = oe o′

infixl 24 _⋆_
_⋆_ : iz ⊑ jz → jz ⊑ kz → iz ⊑ kz
θ      ⋆ (ϕ o′) = (θ ⋆ ϕ) o′
(θ o′) ⋆ (ϕ os) = (θ ⋆ ϕ) o′
(θ os) ⋆ (ϕ os) = (θ ⋆ ϕ) os
oz     ⋆ oz     = oz

Δ₊ : Category ℓ ℓ 0ℓ
Δ₊ = record
  { Obj = Bwd 𝐾
  ; _⇒_ = _⊑_
  ; _≈_ = λ _ _ → ⊤ -- it's a thin category, trust me
  ; id = oi
  ; _∘_ = λ f g → g ⋆ f
  ; assoc = tt
  ; sym-assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; identity² = tt
  ; equiv = record
    { refl = tt
    ; sym = λ _ → tt
    ; trans = λ _ _ → tt
    }
  ; ∘-resp-≈ = λ _ _ → tt
  }

weaken : (kz : Bwd 𝐾) → Endofunctor Δ₊
weaken kz = record
  { F₀ = _++ kz
  ; F₁ = _++⊑ oi
  ; identity = tt
  ; homomorphism = tt
  ; F-resp-≈ = λ _ → tt
  }

thinScoped : {T : Functor Δ₊ (Sets ℓ₁)} → iz ⊑ jz → T .F₀ iz → T .F₀ jz
thinScoped {T = T} θ = T .F₁ θ

weakenScopedRight : {T : Functor Δ₊ (Sets ℓ₁)} → T .F₀ iz → T .F₀ (iz ++ kz)
weakenScopedRight {T = T} = T .F₁ (oi ++⊑ oe)

module _ where

  private variable
    θ θ′ : iz ⊑ jz
    ϕ : jz ⊑ kz
    ψ : iz ⊑ kz

  data Tri : iz ⊑ jz → jz ⊑ kz → iz ⊑ kz → Set where
    _t-″  : Tri θ ϕ ψ → Tri θ               (_o′ {k = k} ϕ) (ψ o′)
    _t′s′ : Tri θ ϕ ψ → Tri (_o′ {k = k} θ) (ϕ os)          (ψ o′)
    _tsss : Tri θ ϕ ψ → Tri (_os {k = k} θ) (ϕ os)          (ψ os)
    tzzz  :             Tri oz              oz              oz

  tri : (θ : iz ⊑ jz) → (ϕ : jz ⊑ kz) → Tri θ ϕ (θ ⋆ ϕ)
  tri (θ o′) (ϕ o′) = tri (θ o′) ϕ t-″
  tri (θ o′) (ϕ os) = tri θ ϕ t′s′
  tri (θ os) (ϕ o′) = tri (θ os) ϕ t-″
  tri (θ os) (ϕ os) = tri θ ϕ tsss
  tri oz     (ϕ o′) = tri oz ϕ t-″
  tri oz     oz     = tzzz

  comp : Tri θ ϕ ψ → ψ ≡ θ ⋆ ϕ
  comp (p t-″ ) = comp p |> cong _o′
  comp (p t′s′) = comp p |> cong _o′
  comp (p tsss) = comp p |> cong _os
  comp tzzz     = refl

  triU : Tri θ ϕ ψ → Tri θ′ ϕ ψ → θ ≡ θ′
  triU (p t-″ ) (q t-″ ) = triU p q
  triU (p t′s′) (q t′s′) = triU p q |> cong _o′
  triU (p tsss) (q tsss) = triU p q |> cong _os
  triU tzzz     tzzz     = refl

module _ where
  private variable
    θ : iz ⊑ ijz
    θ′ : iz′ ⊑ ijz′
    ϕ : jz ⊑ ijz
    ϕ′ : jz′ ⊑ ijz′

  data Coverᵣ : iz ⊑ ijz → jz ⊑ ijz → Set ℓ where
    _c′s : Coverᵣ θ ϕ → Coverᵣ (_o′ {k = k} θ) (ϕ os)
    _cs′ : Coverᵣ θ ϕ → Coverᵣ (_os {k = k} θ) (ϕ o′)
    _css : Coverᵣ θ ϕ → Coverᵣ (_os {k = k} θ) (ϕ os)
    czz  :              Coverᵣ oz              oz

  infix 0 _linearly-covers_
  _linearly-covers_ : Coverᵣ θ ϕ → (ψ : kz ⊑ ijz) → Bool
  czz   linearly-covers ψ    = true
  c c′s linearly-covers ψ o′ = c linearly-covers ψ
  c cs′ linearly-covers ψ o′ = c linearly-covers ψ
  c css linearly-covers ψ o′ = c linearly-covers ψ
  c c′s linearly-covers ψ os = c linearly-covers ψ
  c cs′ linearly-covers ψ os = c linearly-covers ψ
  c css linearly-covers ψ os = false
  _     linearly-covers oz   = true

  pattern !_ t = _ , t

  cie : Coverᵣ (oi {kz = ijz}) oe
  cie {[]}       = czz
  cie {ijz -, _} = cie cs′

  _++c_ : Coverᵣ θ ϕ → Coverᵣ θ′ ϕ′ → Coverᵣ (θ ++⊑ θ′) (ϕ ++⊑ ϕ′)
  c₁ ++c (c₂ c′s) = (c₁ ++c c₂) c′s
  c₁ ++c (c₂ cs′) = (c₁ ++c c₂) cs′
  c₁ ++c (c₂ css) = (c₁ ++c c₂) css
  c₁ ++c czz      = c₁

_∐_ : (θ : iz ⊑ kz) (ϕ : jz ⊑ kz) →
         Σ _ λ ijz → Σ (ijz ⊑ kz) λ ψ → Σ (iz ⊑ ijz) λ θ′ → Σ (jz ⊑ ijz) λ ϕ′ →
         Tri θ′ ψ θ × (Coverᵣ θ′ ϕ′) × Tri ϕ′ ψ ϕ
(θ o′) ∐ (ϕ o′) = let ! ! ! ! (tl , c , tr) = θ ∐ ϕ in ! ! ! ! (tl t-″ , c , tr t-″)
(θ o′) ∐ (ϕ os) with θ ∐ ϕ
... | ! ! ! ! (tl , c , tr) = ! ! ! ! (tl t′s′ , c c′s , tr tsss)
(θ os) ∐ (ϕ o′) with θ ∐ ϕ
... | ! ! ! ! (tl , c , tr) = ! ! ! ! (tl tsss , c cs′ , tr t′s′)
(θ os) ∐ (ϕ os) with θ ∐ ϕ
... | ! ! ! ! (tl , c , tr) = ! ! ! ! (tl tsss , c css , tr tsss)
oz ∐ oz = ! ! ! ! (tzzz , czz , tzzz)

module _ where
  private variable
    θ′ : iz′ ⊑ kz′
    ϕ′ : jz′ ⊑ kz′

  subCop : ∀ {θ′ : iz′ ⊑ kz′} {ϕ′ : jz′ ⊑ kz′} → (ψ : kz ⊑ kz′) → Coverᵣ θ′ ϕ′ →
              Σ _ λ iz → Σ _ λ jz → Σ (iz ⊑ kz) λ θ → Σ (jz ⊑ kz) λ ϕ → Σ (iz ⊑ iz′) λ ψ₀ → Σ (jz ⊑ jz′) λ ψ₁ → Coverᵣ θ ϕ
  subCop (ψ o′) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ o′ , c′)
  subCop (ψ o′) (c cs′) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ o′ , ψ₁ , c′)
  subCop (ψ o′) (c css) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ o′ , ψ₁ o′ , c′)
  subCop (ψ os) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ os , c′ c′s)
  subCop (ψ os) (c cs′) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ os , ψ₁ , c′ cs′)
  subCop (ψ os) (c css) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ os , ψ₁ os , c′ css)
  subCop {θ′ = oz} {ϕ′ = oz} oz c = ! ! ! ! (oz , oz , c)

lrCop : (iz jz : Bwd 𝐾) → Σ (iz ⊑ (iz ++ jz)) λ θ → Σ (jz ⊑ (iz ++ jz)) λ ϕ → Coverᵣ θ ϕ
lrCop iz []        = ! ! cie
lrCop iz (jz -, _) = let ! ! c = lrCop iz jz in ! ! (c c′s)

_⊣_ : ∀ {iz kz} jz → (ψ : iz ⊑ (kz ++ jz)) → Σ _ λ kz′ → Σ _ λ jz′ → Σ (kz′ ⊑ kz) λ θ → Σ (jz′ ⊑ jz) λ ϕ → Σ (iz ≡ (kz′ ++ jz′)) λ { refl → ψ ≡ (θ ++⊑ ϕ)}
[] ⊣ ψ = ! ! (ψ , oz , refl , refl)
(jz -, _) ⊣ (ψ o′) with jz ⊣ ψ
... | ! ! (θ , ϕ , refl , refl) = ! ! (θ , ϕ o′ , refl , refl)
(jz -, _) ⊣ (ψ os) with jz ⊣ ψ
... | ! ! (θ , ϕ , refl , refl) = ! ! (θ , ϕ os , refl , refl)

Scoped : (ℓ₁ : Level) → Set (ℓ ⊔ suc ℓ₁)
Scoped = Pred (Bwd 𝐾)

infixl 15 _⇑_
infixl 14 _↑_
record _⇑_ (T : Scoped ℓ₁) (scope : Bwd 𝐾) : Set (ℓ ⊔ ℓ₁) where
  constructor _↑_
  field
    { support } : Bwd 𝐾
    thing       : T support
    thinning    : support ⊑ scope
open _⇑_ public

private variable
  S T : Scoped ℓ

map⇑ : ∀[ S    ⇒ T    ] →
       ∀[ S ⇑_ ⇒ T ⇑_ ]
map⇑ f (s ↑ θ) = f s ↑ θ

mult⇑ : ∀[ S ⇑_ ⇑_ ⇒ S ⇑_ ]
mult⇑ ((thing ↑ θ′) ↑ θ) = thing ↑ (θ′ ⋆ θ)

thin⇑ : iz ⊑ jz → S ⇑ iz → S ⇑ jz
thin⇑ θ x = mult⇑ (x ↑ θ)

data Oneᵣ : Scoped ℓ where
  ⟨⟩ : Oneᵣ []

⟨⟩ᵣ : Oneᵣ ⇑ kz
⟨⟩ᵣ = ⟨⟩ ↑ oe

data _⊢_ jz (T : Scoped ℓ) kz : Set ℓ where
  _⑊_ : iz ⊑ jz → T (kz ++ iz) → (jz ⊢ T) kz

_⑊ᵣ_ : ∀ jz → T ⇑ (kz ++ jz) → (jz ⊢ T) ⇑ kz
jz ⑊ᵣ (t ↑ ψ) with jz ⊣ ψ
... | ! ! (θ , ϕ , refl , refl) = (ϕ ⑊ t) ↑ θ

infixl 16 _×ᵣ_
record _×ᵣ_ (S T : Scoped ℓ) (ijz : Bwd 𝐾) : Set ℓ where
  constructor pair
  field
    outl : S ⇑ ijz
    outr : T ⇑ ijz
    cover : Coverᵣ (outl .thinning) (outr .thinning)

_,ᵣ_ : {S T : Scoped _} → S ⇑ kz → T ⇑ kz → (S ×ᵣ T) ⇑ kz
(s ↑ θ) ,ᵣ (t ↑ ϕ) = let _ , ψ , θ′ , ϕ′ , _ , c , _ = θ ∐ ϕ in pair (s ↑ θ′) (t ↑ ϕ′) c ↑ ψ

outlᵣ : {S T : Scoped _} → (S ×ᵣ T) ⇑ kz → S ⇑ kz
outlᵣ (pair s _ _ ↑ ψ) = thin⇑ ψ s

outrᵣ : {S T : Scoped _} → (S ×ᵣ T) ⇑ kz → T ⇑ kz
outrᵣ (pair _ t _ ↑ ψ) = thin⇑ ψ t

data Vaᵣ (k : 𝐾) : Scoped ℓ where
  only : Vaᵣ k ([] -, k)

vaᵣ : (k ⟵ kz) → Vaᵣ k ⇑ kz
vaᵣ θ = only ↑ θ
