{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
open import Level using (Level; _⊔_; 0ℓ)

module Data.Scoped
  {ℓ : Level}
  (𝐾 : Set ℓ)
  where

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)
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
  iz iz′ jz jz′ kz kz′ ijz ijz′ : Bwd 𝐾

infixr 19 _⊑_
data _⊑_ : Bwd 𝐾 → Bwd 𝐾 → Set where
  _o′ : iz ⊑ jz →  iz        ⊑ (jz -, k)
  _os : iz ⊑ jz → (iz -, k) ⊑ (jz -, k)
  oz :               []        ⊑  []

_⟵_ : 𝐾 → Bwd 𝐾 → Set
k ⟵ kz = ([] -, k) ⊑ kz

_⧺⊑_ : iz ⊑ jz → iz′ ⊑ jz′ → (iz ⧺ iz′) ⊑ (jz ⧺ jz′)
θ ⧺⊑ (ϕ o′) = (θ ⧺⊑ ϕ) o′
θ ⧺⊑ (ϕ os) = (θ ⧺⊑ ϕ) os
θ ⧺⊑ oz = θ

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

Δ₊ : Category ℓ 0ℓ 0ℓ
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
  ) hiding (map⇑; unit⇑; mult⇑; thin⇑; SlicedFunctor) public
open _⇑′_ public

module _ where
  private variable
    θ : iz ⊑ ijz
    θ′ : iz′ ⊑ ijz′
    ϕ : jz ⊑ ijz
    ϕ′ : jz′ ⊑ ijz′
    wss s₁ s₂ : Substructure

  data Coverₒ : iz ⊑ ijz → jz ⊑ ijz → Set where
    _c′s : Coverₒ θ ϕ → Coverₒ (_o′ {k = k} θ) (ϕ os)
    czi : (p : ϕ ≡ oe) → Coverₒ oi ϕ

  data Coverₗ : iz ⊑ ijz → jz ⊑ ijz → Set where
    _c′s : Coverₗ θ ϕ → Coverₗ (_o′ {k = k} θ) (ϕ os)
    _cs′ : Coverₗ θ ϕ → Coverₗ (_os {k = k} θ) (ϕ o′)
    czz : Coverₗ oz oz

  data Coverᵣ : iz ⊑ ijz → jz ⊑ ijz → Set where
    _c′s : Coverᵣ θ ϕ → Coverᵣ (_o′ {k = k} θ) (ϕ os)
    _cs′ : Coverᵣ θ ϕ → Coverᵣ (_os {k = k} θ) (ϕ o′)
    _css : Coverᵣ θ ϕ → Coverᵣ (_os {k = k} θ) (ϕ os)
    czz : Coverᵣ oz oz

  Coverₛ : iz ⊑ ijz → jz ⊑ ijz → Substructured _
  Coverₛ θ ϕ Ordered = Coverₒ θ ϕ
  Coverₛ θ ϕ Linear = Coverₗ θ ϕ
  Coverₛ θ ϕ Relevant = Coverᵣ θ ϕ
  Coverₛ _ _ Unrestricted = ⊤

  pattern !_ t = _ , t

  -- _⧺cₒ_ : Coverₛ θ ϕ Ordered → Coverₛ θ′ ϕ′ Ordered → Σ ((iz ⧺ iz′) ⊑ (ijz ⧺ ijz′)) λ ψ → Σ ((jz ⧺ jz′) ⊑ (ijz ⧺ ijz′)) λ ψ′ → Coverₛ ψ ψ′ Ordered
  -- c₁ ⧺cₒ c₂ = {!!}

  -- _⧺cₗ_ : Coverₛ θ ϕ s₁ → Coverₛ θ′ ϕ′ s₂ → Coverₛ (θ ⧺⊑ θ′) (ϕ ⧺⊑ ϕ′) ⇑′ (Linear ⊔ s₁ ⊔ s₂)
  -- c₁ ⧺cₗ c₂ = {!!}

  cie : Coverₛ (oi {kz = ijz}) oe wss
  cie {_} {Ordered} = czi refl
  cie {[]} {Linear} = czz
  cie {ijz -, _} {Linear} = cie cs′
  cie {[]} {Relevant} = czz
  cie {ijz -, _} {Relevant} = cie cs′
  cie {_} {Unrestricted} = tt

  cover-ordered-to-linear : Coverₛ θ ϕ Ordered → Coverₛ θ ϕ Linear
  cover-ordered-to-linear (c c′s) = cover-ordered-to-linear c c′s
  cover-ordered-to-linear (czi refl) = cie

  cover-linear-to-relevant : Coverₛ θ ϕ Linear → Coverₛ θ ϕ Relevant
  cover-linear-to-relevant (c c′s) = cover-linear-to-relevant c c′s
  cover-linear-to-relevant (c cs′) = cover-linear-to-relevant c cs′
  cover-linear-to-relevant czz = czz

  cover-weaken : {f : SubstructureCat [ s₁ , s₂ ]} → Coverₛ θ ϕ s₁ → Coverₛ θ ϕ s₂
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

-- CoverFunctor : (θ : iz ⊑ ijz) → (ϕ : jz ⊑ ijz) → Functor SubstructureCat (Sets ℓ)
-- CoverFunctor θ ϕ = record
--   { F₀ = Coverₛ θ ϕ
--   ; F₁ = λ f → cover-weaken {f = f}
--   ; identity = {!!}
--   ; homomorphism = {!!}
--   ; F-resp-≈ = {!!}
--  }

_∐_ : (θ : iz ⊑ kz) (ϕ : jz ⊑ kz) →
         Σ _ λ ijz → Σ (ijz ⊑ kz) λ ψ → Σ (iz ⊑ ijz) λ θ′ → Σ (jz ⊑ ijz) λ ϕ′ →
         Tri θ′ ψ θ × (Coverₛ θ′ ϕ′ ⇑′ Relevant) × Tri ϕ′ ψ ϕ
(θ o′) ∐ (ϕ o′) = let ! ! ! ! (tl , c , tr) = θ ∐ ϕ in ! ! ! ! (tl t-″ , c , tr t-″)
(θ o′) ∐ (ϕ os) with θ ∐ ϕ
... | ! ! ! ! (tl , _↑′_ {support = Ordered} c _ , tr) = ! ! ! ! (tl t′s′ , _↑′_ {support = Ordered} (c c′s) tt , tr tsss)
... | ! ! ! ! (tl , _↑′_ {support = Linear} c _ , tr) = ! ! ! ! (tl t′s′ , _↑′_ {support = Linear} (c c′s) tt , tr tsss)
... | ! ! ! ! (tl , _↑′_ {support = Relevant} c _ , tr) = ! ! ! ! (tl t′s′ , _↑′_ {support = Relevant} (c c′s) tt , tr tsss)
(θ os) ∐ (ϕ o′) with θ ∐ ϕ
... | ! ! ! ! (tl , _↑′_ {support = Ordered} (c c′s) _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Linear} (cover-weaken c c′s cs′) tt , tr t′s′)
... | ! ! ! ! (tl , _↑′_ {support = Ordered} (czi refl) _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Ordered} (czi refl) tt , tr t′s′)
... | ! ! ! ! (tl , _↑′_ {support = Linear} c _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Linear} (c cs′) tt , tr t′s′)
... | ! ! ! ! (tl , _↑′_ {support = Relevant} c _ , tr) = ! ! ! ! (tl tsss , _↑′_ {support = Relevant} (c cs′) tt , tr t′s′)
(θ os) ∐ (ϕ os) with θ ∐ ϕ
... | ! ! ! ! (tl , _↑′_ {support = Ordered} c _ , tr) = ! ! ! ! ((tl tsss , cover-weaken c css ↑′ tt , tr tsss))
... | ! ! ! ! (tl , _↑′_ {support = Linear} c _ , tr) = ! ! ! ! (tl tsss , cover-weaken c css ↑′ tt , tr tsss)
... | ! ! ! ! (tl , _↑′_ {support = Relevant} c _ , tr) = ! ! ! ! (tl tsss , c css ↑′ tt , tr tsss)
oz ∐ oz = ! ! ! ! (tzzz , czi refl ↑′ tt , tzzz)

module _ where
  private variable
    θ′ : iz′ ⊑ kz′
    ϕ′ : jz′ ⊑ kz′
    wss : Substructure

  subCop : ∀ {θ′ : iz′ ⊑ kz′} {ϕ′ : jz′ ⊑ kz′} → (ψ : kz ⊑ kz′) → Coverₛ θ′ ϕ′ wss →
              Σ _ λ iz → Σ _ λ jz → Σ (iz ⊑ kz) λ θ → Σ (jz ⊑ kz) λ ϕ → Σ (iz ⊑ iz′) λ ψ₀ → Σ (jz ⊑ jz′) λ ψ₁ → Coverₛ θ ϕ wss
  subCop {wss = Ordered} (ψ o′) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ o′ , c′)
  subCop {wss = Ordered} (ψ o′) (czi refl) = _ , [] , _ , oe , ψ o′ , oe , cie
  subCop {wss = Linear} (ψ o′) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ o′ , c′)
  subCop {wss = Linear} (ψ o′) (c cs′) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ o′ , ψ₁ , c′)
  subCop {wss = Relevant} (ψ o′) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ o′ , c′)
  subCop {wss = Relevant} (ψ o′) (c cs′) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ o′ , ψ₁ , c′)
  subCop {wss = Relevant} (ψ o′) (c css) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ o′ , ψ₁ o′ , c′)
  subCop {wss = Unrestricted} (ψ o′) _ = [] , [] , oe , oe , oe , oe , tt -- you choose weak guarantees — you get trivial subcover
  subCop {wss = Ordered} (ψ os) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ os , c′ c′s)
  subCop {wss = Ordered} (ψ os) (czi refl) = _ , [] , _ , oe , ψ os , oe , cie
  subCop {wss = Linear} (ψ os) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ os , c′ c′s)
  subCop {wss = Linear} (ψ os) (c cs′) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ os , ψ₁ , c′ cs′)
  subCop {wss = Relevant} (ψ os) (c c′s) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ , ψ₁ os , c′ c′s)
  subCop {wss = Relevant} (ψ os) (c cs′) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ os , ψ₁ , c′ cs′)
  subCop {wss = Relevant} (ψ os) (c css) = let ! ! ! ! (ψ₀ , ψ₁ , c′) = subCop ψ c in ! ! ! ! (ψ₀ os , ψ₁ os , c′ css)
  subCop {wss = Unrestricted} (ψ os) c = [] , [] , oe , oe , oe , oe , tt -- same here
  subCop {θ′ = oz} {ϕ′ = oz} oz c = ! ! ! ! (oz , oz , c)

lrCop : (iz jz : Bwd 𝐾) → Σ (iz ⊑ (iz ⧺ jz)) λ θ → Σ (jz ⊑ (iz ⧺ jz)) λ ϕ → Coverₛ θ ϕ Ordered
lrCop iz [] = ! ! cie
lrCop iz (jz -, j) = let ! ! c = lrCop iz jz in ! ! (c c′s)

_⊣_ : ∀ {iz kz} jz → (ψ : iz ⊑ (kz ⧺ jz)) → Σ _ λ kz′ → Σ _ λ jz′ → Σ (kz′ ⊑ kz) λ θ → Σ (jz′ ⊑ jz) λ ϕ → Σ (iz ≡ (kz′ ⧺ jz′)) λ { refl → ψ ≡ (θ ⧺⊑ ϕ)}
[] ⊣ ψ = ! ! (ψ , oz , refl , refl)
(jz -, _) ⊣ (ψ o′) with jz ⊣ ψ
... | ! ! (θ , ϕ , refl , refl) = ! ! (θ , ϕ o′ , refl , refl)
(jz -, _) ⊣ (ψ os) with jz ⊣ ψ
... | ! ! (θ , ϕ , refl , refl) = ! ! (θ , ϕ os , refl , refl)

open import Data.Sliced Δ₊ using (_⇑_; _↑_; thin⇑) renaming (CPred to Scoped) public
open _⇑_ public

data Oneₛ : Scoped ℓ where
  ⟨⟩ : Oneₛ []

⟨⟩ₛ : Oneₛ ⇑ kz
⟨⟩ₛ = ⟨⟩ ↑ oe

data _⊢_ jz (T : Scoped ℓ) kz : Set ℓ where
  _⑊_ : iz ⊑ jz → T (kz ⧺ iz) → (jz ⊢ T) kz

private variable
  S T : Scoped ℓ

_⑊ₛ_ : ∀ jz → T ⇑ (kz ⧺ jz) → (jz ⊢ T) ⇑ kz
jz ⑊ₛ (t ↑ ψ) with jz ⊣ ψ
... | ! ! (θ , ϕ , refl , refl) = (ϕ ⑊ t) ↑ θ

infixl 16 _×ₛ_
record _×ₛ_ (S T : Scoped ℓ) {wss : Substructure} (ijz : Bwd 𝐾) : Set ℓ where
  constructor pair
  field
    outl : S ⇑ ijz
    outr : T ⇑ ijz
    cover : Coverₛ (outl .thinning) (outr .thinning) ⇑′ wss

infixl 16 _×ₒ_
_×ₒ_ : (S T : Scoped ℓ) → Scoped ℓ
S ×ₒ T = (S ×ₛ T) {Ordered}

infixl 16 _×ₗ_
_×ₗ_ : (S T : Scoped ℓ) → Scoped ℓ
S ×ₗ T = (S ×ₛ T) {Linear}

infixl 16 _×ᵣ_
_×ᵣ_ : (S T : Scoped ℓ) → Scoped ℓ
S ×ᵣ T = (S ×ₛ T) {Relevant}

_,ᵣ_ : {S T : Scoped _} → S ⇑ kz → T ⇑ kz → (S ×ᵣ T) ⇑ kz
(s ↑ θ) ,ᵣ (t ↑ ϕ) = let _ , ψ , θ′ , ϕ′ , _ , c , _ = θ ∐ ϕ in pair (s ↑ θ′) (t ↑ ϕ′) c ↑ ψ

outlₛ : {wss : Substructure} → {S T : Scoped _} → (S ×ₛ T) {wss} ⇑ kz → S ⇑ kz
outlₛ (pair s _ _ ↑ ψ) = thin⇑ ψ s

outrₛ : {wss : Substructure} → {S T : Scoped _} → (S ×ₛ T) {wss} ⇑ kz → T ⇑ kz
outrₛ (pair _ t _ ↑ ψ) = thin⇑ ψ t

data Vaᵣ (k : 𝐾) : Scoped ℓ where
  only : Vaᵣ k ([] -, k)

vaᵣ : ([] -, k) ⊑ kz → Vaᵣ k ⇑ kz
vaᵣ θ = only ↑ θ
