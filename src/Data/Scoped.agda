open import Level using (Level; _⊔_; suc)

module Data.Scoped
  {o ℓ e : Level}
  (𝐾 : Set o)
  where

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)
-- open Category
open import Data.Bwd using (Bwd; []; _-,_)
-- open import Data.Sliced
open Functor using (F₀; F₁)
open import Relation.Unary using (Pred)

infixr 19 _⊑_
data _⊑_ : Bwd 𝐾 → Bwd 𝐾 → Set ℓ where
  _o′ : {iz jz : Bwd 𝐾} → {k : 𝐾} → iz ⊑ jz →  iz        ⊑ (jz -, k)
  _os : {iz jz : Bwd 𝐾} → {k : 𝐾} → iz ⊑ jz → (iz -, k) ⊑ (jz -, k)
  oz :                                                  []        ⊑  []

oi : {kz : Bwd 𝐾} → kz ⊑ kz
oi {[]} = oz
oi {kz -, _} = oi os

infixl 24 _⋆_
_⋆_ : {iz jz kz : Bwd 𝐾} → iz ⊑ jz → jz ⊑ kz → iz ⊑ kz
θ       ⋆ (ϕ o′) = (θ ⋆ ϕ) o′
(θ o′) ⋆ (ϕ os) = (θ ⋆ ϕ) o′
(θ os) ⋆ (ϕ os) = (θ ⋆ ϕ) os
oz      ⋆ oz = oz

Δ₊ : Category o ℓ e
Δ₊ = record
  { Obj = Bwd 𝐾
  ; _⇒_ = _⊑_
  ; _≈_ = {!!}
  ; id = oi
  ; _∘_ = λ f g → g ⋆ f
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }

Scoped : (ℓ₁ : Level) → Set (o ⊔ suc ℓ₁)
Scoped ℓ₁ = Pred (Bwd 𝐾) ℓ₁

thinScoped : ∀ {ℓ₁} → {T : Functor Δ₊ (Sets ℓ₁)} → {iz jz : Bwd 𝐾} → iz ⊑ jz → T .F₀ iz → T .F₀ jz
thinScoped {T = T} θ = T .F₁ θ

weakenScoped : ∀ {ℓ₁} → {T : Functor Δ₊ (Sets ℓ₁)} → {iz : Bwd 𝐾} → {k : 𝐾} → T .F₀ iz → T .F₀ (iz -, k)
weakenScoped {T = T} = T .F₁ (oi o′)

-- _⇧_ = 
