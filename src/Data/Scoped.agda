{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
open import Level using (Level; _⊔_; suc; 0ℓ)

module Data.Scoped
  {ℓ : Level}
  (𝐾 : Set ℓ)
  where

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)
open import Data.Bool using (Bool; false; true)
open import Data.Bwd using (Bwd; []; _-,_; _⧺_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Substructure using (Ordered; Linear; Substructure; Relevant; SubstructureCat; Unrestricted)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (_|>_)
open Functor using (F₀; F₁)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Relation.Unary using (Pred)

private variable
  ℓ₁ : Level
  k : 𝐾
  iz iz′ jz jz′ kz ijz ijz′ : Bwd 𝐾

infixr 19 _⊑_
data _⊑_ : Bwd 𝐾 → Bwd 𝐾 → Set ℓ where
  _o′ : iz ⊑ jz →  iz        ⊑ (jz -, k)
  _os : iz ⊑ jz → (iz -, k) ⊑ (jz -, k)
  oz :               []        ⊑  []

_⧺ₒ_ : iz ⊑ jz → iz′ ⊑ jz′ → (iz ⧺ iz′) ⊑ (jz ⧺ jz′)
θ ⧺ₒ (ϕ o′) = (θ ⧺ₒ ϕ) o′
θ ⧺ₒ (ϕ os) = (θ ⧺ₒ ϕ) os
θ ⧺ₒ oz = θ

oi : kz ⊑ kz
oi {[]} = oz
oi {kz -, _} = oi os

oe : [] ⊑ kz
oe {[]} = oz
oe {kz -, k} = oe o′

infixl 24 _⋆_
_⋆_ : iz ⊑ jz → jz ⊑ kz → iz ⊑ kz
θ       ⋆ (ϕ o′) = (θ ⋆ ϕ) o′
(θ o′) ⋆ (ϕ os) = (θ ⋆ ϕ) o′
(θ os) ⋆ (ϕ os) = (θ ⋆ ϕ) os
oz      ⋆ oz = oz

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

thinScoped : {T : Functor Δ₊ (Sets ℓ₁)} → iz ⊑ jz → T .F₀ iz → T .F₀ jz
thinScoped {T = T} θ = T .F₁ θ

weakenScoped : {T : Functor Δ₊ (Sets ℓ₁)} → T .F₀ iz → T .F₀ (iz -, k)
weakenScoped {T = T} = T .F₁ (oi o′)

module _ where

  private variable
    θ θ′ : iz ⊑ jz
    ϕ : jz ⊑ kz
    ψ : iz ⊑ kz

  data Tri : iz ⊑ jz → jz ⊑ kz → iz ⊑ kz → Set where
    _t-″ : Tri θ ϕ ψ → Tri θ (_o′ {k = k} ϕ) (ψ o′)
    _t′s′ : Tri θ ϕ ψ → Tri (_o′ {k = k} θ) (ϕ os) (ψ o′)
    _tsss : Tri θ ϕ ψ → Tri (_os {k = k} θ) (ϕ os) (ψ os)
    tzzz : Tri oz oz oz

  tri : (θ : iz ⊑ jz) → (ϕ : jz ⊑ kz) → Tri θ ϕ (θ ⋆ ϕ)
  tri (θ o′) (ϕ o′) = tri (θ o′) ϕ t-″
  tri (θ o′) (ϕ os) = tri θ ϕ t′s′
  tri (θ os) (ϕ o′) = tri (θ os) ϕ t-″
  tri (θ os) (ϕ os) = tri θ ϕ tsss
  tri oz (ϕ o′) = tri oz ϕ t-″
  tri oz oz = tzzz

  comp : Tri θ ϕ ψ → ψ ≡ θ ⋆ ϕ
  comp (p t-″) = comp p |> cong _o′
  comp (p t′s′) = comp p |> cong _o′
  comp (p tsss) = comp p |> cong _os
  comp tzzz = refl

  triU : Tri θ ϕ ψ → Tri θ′ ϕ ψ → θ ≡ θ′
  triU (p t-″) (q t-″) = triU p q
  triU (p t′s′) (q t′s′) = triU p q |> cong _o′
  triU (p tsss) (q tsss) = triU p q |> cong _os
  triU tzzz tzzz = refl

open import Data.Sliced SubstructureCat renaming
  ( CPred to Substructured
  ; _⇑_ to _⇑′_
  ; _↑_ to _↑′_
  ; map⇑ to map⇑′
  ; unit⇑ to unit⇑′
  ; mult⇑ to mult⇑′
  ; thin⇑ to thin⇑′
  ) hiding (SlicedFunctor) public
open _⇑′_ public

module _ where

  private variable
    sh : Bool
    θ : iz ⊑ ijz
    θ′ : iz′ ⊑ ijz′
    ϕ : jz ⊑ ijz
    ϕ′ : jz′ ⊑ ijz′
    wss s₁ s₂ : Substructure

  data Coverₒ′ : iz ⊑ ijz → jz ⊑ ijz → Bool → Set ℓ where
    _c′s : Coverₒ′ θ ϕ sh → Coverₒ′ (_o′ {k = k} θ) (ϕ os) true
    _cs′ : Coverₒ′ θ ϕ false → Coverₒ′ (_os {k = k} θ) (ϕ o′) false
    czz : Coverₒ′ oz oz false

  Coverₒ : iz ⊑ ijz → jz ⊑ ijz → Set ℓ
  Coverₒ θ ϕ = Σ Bool (Coverₒ′ θ ϕ)

  data Coverₗ : iz ⊑ ijz → jz ⊑ ijz → Set ℓ where
    _c′s : Coverₗ θ ϕ → Coverₗ (_o′ {k = k} θ) (ϕ os)
    _cs′ : Coverₗ θ ϕ → Coverₗ (_os {k = k} θ) (ϕ o′)
    czz : Coverₗ oz oz

  data Coverᵣ : iz ⊑ ijz → jz ⊑ ijz → Set ℓ where
    _c′s : Coverᵣ θ ϕ → Coverᵣ (_o′ {k = k} θ) (ϕ os)
    _cs′ : Coverᵣ θ ϕ → Coverᵣ (_os {k = k} θ) (ϕ o′)
    _css : Coverᵣ θ ϕ → Coverᵣ (_os {k = k} θ) (ϕ os)
    czz : Coverᵣ oz oz

  Coverₛ : iz ⊑ ijz → jz ⊑ ijz → Substructured ℓ
  Coverₛ θ ϕ Ordered = Coverₒ θ ϕ
  Coverₛ θ ϕ Linear = Coverₗ θ ϕ
  Coverₛ θ ϕ Relevant = Coverᵣ θ ϕ
  Coverₛ _ _ Unrestricted = ⊤

  pattern !_ t = _ , t

  _⧺ᵥ_ : Coverₛ θ ϕ wss → Coverₛ θ′ ϕ′ wss → Coverₛ (θ ⧺ₒ θ′) (ϕ ⧺ₒ ϕ′) wss
  _⧺ᵥ_ {wss = Ordered} c₁ (.true , (c₂ c′s)) = let ! ind = c₁ ⧺ᵥ ( ! c₂) in true , ind c′s
  _⧺ᵥ_ {wss = Ordered} c₁ (.false , (c₂ cs′)) = {!!} -- TODO
  _⧺ᵥ_ {wss = Ordered} c₁ (.false , czz) = c₁
  _⧺ᵥ_ {wss = Linear} c₁ (c₂ c′s) = (c₁ ⧺ᵥ c₂) c′s
  _⧺ᵥ_ {wss = Linear} c₁ (c₂ cs′) = (c₁ ⧺ᵥ c₂) cs′
  _⧺ᵥ_ {wss = Linear} c₁ czz = c₁
  _⧺ᵥ_ {wss = Relevant} c₁ (c₂ c′s) = (c₁ ⧺ᵥ c₂) c′s
  _⧺ᵥ_ {wss = Relevant} c₁ (c₂ cs′) = (c₁ ⧺ᵥ c₂) cs′
  _⧺ᵥ_ {wss = Relevant} c₁ (c₂ css) = (c₁ ⧺ᵥ c₂) css
  _⧺ᵥ_ {wss = Relevant} c₁ czz = c₁
  _⧺ᵥ_ {wss = Unrestricted} _ _ = tt

  cover-ordered-to-linear : Coverₛ θ ϕ Ordered → Coverₛ θ ϕ Linear
  cover-ordered-to-linear (false , c cs′) = cover-ordered-to-linear (false , c) cs′
  cover-ordered-to-linear (false , czz) = czz
  cover-ordered-to-linear (true , _c′s {sh = sh} c) = cover-ordered-to-linear (sh , c) c′s

  cover-linear-to-relevant : Coverₛ θ ϕ Linear → Coverₛ θ ϕ Relevant
  cover-linear-to-relevant (c c′s) = cover-linear-to-relevant c c′s
  cover-linear-to-relevant (c cs′) = cover-linear-to-relevant c cs′
  cover-linear-to-relevant czz = czz

  cover-weaken : {SubstructureCat [ s₁ , s₂ ]} → Coverₛ θ ϕ s₁ → Coverₛ θ ϕ s₂
  cover-weaken {s₁ = Ordered} {s₂ = Ordered} c = c
  cover-weaken {s₁ = Ordered} {s₂ = Linear} c = cover-ordered-to-linear c
  cover-weaken {s₁ = Ordered} {s₂ = Relevant} c = cover-linear-to-relevant (cover-ordered-to-linear c)
  cover-weaken {s₁ = Ordered} {s₂ = Unrestricted} _ = tt
  cover-weaken {s₁ = Linear} {s₂ = Linear} c = c
  cover-weaken {s₁ = Linear} {s₂ = Relevant} c = cover-linear-to-relevant c
  cover-weaken {s₁ = Linear} {s₂ = Unrestricted} _ = tt
  cover-weaken {s₁ = Relevant} {s₂ = Relevant} c = c
  cover-weaken {s₁ = Relevant} {s₂ = Unrestricted} _ = tt
  cover-weaken {s₁ = Unrestricted} {s₂ = Unrestricted} _ = tt

-- CoverFunctor : (θ : iz ⊑ ijz) → (ϕ : jz ⊑ ijz) → Functor SubstructureCat (Sets o)
-- CoverFunctor θ ϕ = record
--   { F₀ = Coverₛ θ ϕ
--   ; F₁ = {!!}
--   ; identity = {!!}
--   ; homomorphism = {!!}
--   ; F-resp-≈ = {!!}
--   }

_∐_ : (θ : iz ⊑ kz) (ϕ : jz ⊑ kz) →
         Σ _ λ ijz → Σ (ijz ⊑ kz) λ ψ → Σ (iz ⊑ ijz) λ θ′ → Σ (jz ⊑ ijz) λ ϕ′ →
         Tri θ′ ψ θ × (Coverₛ θ′ ϕ′ ⇑′ Relevant) × Tri ϕ′ ψ ϕ
(θ o′) ∐ (ϕ o′) = let ! ! ! ! (tl , c , tr) = θ ∐ ϕ in ! ! ! ! (tl t-″ , c , tr t-″)
(θ o′) ∐ (ϕ os) with θ ∐ ϕ
... | ! ! ! ! (tl , _↑′_ {support = Ordered} (_ , c) _ , tr) = ! ! ! ! ((tl t′s′ , _↑′_ {support = Ordered} (true , c c′s) tt , tr tsss))
... | ! ! ! ! (tl , _↑′_ {support = Linear} c _ , tr) = ! ! ! ! (tl t′s′ , _↑′_ {support = Linear} (c c′s) tt , tr tsss)
... | ! ! ! ! (tl , _↑′_ {support = Relevant} c _ , tr) = ! ! ! ! (tl t′s′ , _↑′_ {support = Relevant} (c c′s) tt , tr tsss)
(θ os) ∐ (ϕ o′) with θ ∐ ϕ
... | ! ! ! ! (tl , _↑′_ {support = Ordered} (false , c) _ , tr) = ! ! ! ! (tl tsss , (false , c cs′) ↑′ tt , tr t′s′)
... | ! ! ! ! (tl , _↑′_ {support = Ordered} (true , c) _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Linear} (cover-weaken (true , c) cs′) tt , tr t′s′)
... | ! ! ! ! (tl , _↑′_ {support = Linear} c _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Linear} (c cs′) tt , tr t′s′)
... | ! ! ! ! (tl , _↑′_ {support = Relevant} c _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Relevant} (c cs′) tt , tr t′s′)
(θ os) ∐ (ϕ os) with θ ∐ ϕ
... | ! ! ! ! (tl , _↑′_ {support = Ordered} c _ , tr) = ! ! ! ! ((tl tsss , cover-weaken c css ↑′ tt , tr tsss))
... | ! ! ! ! (tl , _↑′_ {support = Linear} c _ , tr) = ! ! ! ! (tl tsss , cover-weaken c css ↑′ tt , tr tsss)
... | ! ! ! ! (tl , _↑′_ {support = Relevant} c _ , tr) = ! ! ! ! (tl tsss , c css ↑′ tt , tr tsss)
oz ∐ oz = ! ! ! ! (tzzz , (false , czz) ↑′ tt , tzzz)

lrCop : (iz jz : Bwd 𝐾) → Σ (iz ⊑ (iz ⧺ jz)) λ θ → Σ (jz ⊑ (iz ⧺ jz)) λ ϕ → Coverₛ θ ϕ Ordered
lrCop [] [] = ! ! (false , czz)
lrCop (iz -, _) [] = let ! ! ! c = lrCop iz [] in {!!} -- TODO
lrCop iz (jz -, _) = let ! ! ! c = lrCop iz jz in ! ! (true , c c′s)

open import Data.Sliced Δ₊ public renaming (CPred to Scoped)
open _⇑_ public

data Oneₛ : Scoped ℓ where
  ⟨⟩ : Oneₛ []

⟨⟩ₛ : Oneₛ ⇑ kz
⟨⟩ₛ = ⟨⟩ ↑ oe

record _×ₛ_ (S T : Scoped ℓ) {wss : Substructure} (ijz : Bwd 𝐾) : Set ℓ where
  constructor pair
  field
    outl : S ⇑ ijz
    outr : T ⇑ ijz
    cover : Coverₛ (outl .thinning) (outr .thinning) ⇑′ wss

_×ₒ_ : (S T : Scoped ℓ) → Scoped ℓ
S ×ₒ T = (S ×ₛ T) {Ordered}

_×ₗ_ : (S T : Scoped ℓ) → Scoped ℓ
S ×ₗ T = (S ×ₛ T) {Linear}

_×ᵣ_ : (S T : Scoped ℓ) → Scoped ℓ
S ×ᵣ T = (S ×ₛ T) {Relevant}

_,ᵣ_ : {S T : Scoped _} → S ⇑ kz → T ⇑ kz → (S ×ᵣ T) ⇑ kz
(s ↑ θ) ,ᵣ (t ↑ ϕ) = let _ , ψ , θ′ , ϕ′ , _ , c , _ = θ ∐ ϕ in pair (s ↑ θ′) (t ↑ ϕ′) c ↑ ψ

outlₛ : {wss : Substructure} → {S T : Scoped _} → (S ×ₛ T) {wss} ⇑ kz → S ⇑ kz
outlₛ (pair s _ _ ↑ ψ) = thin⇑ ψ s

outrₛ : {wss : Substructure} → {S T : Scoped _} → (S ×ₛ T) {wss} ⇑ kz → T ⇑ kz
outrₛ (pair _ t _ ↑ ψ) = thin⇑ ψ t

data Var (k : 𝐾) : Scoped ℓ where
  only : Var k ([] -, k)

var : ([] -, k) ⊑ kz → Var k ⇑ kz
var θ = only ↑ θ
