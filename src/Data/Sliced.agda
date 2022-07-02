{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
open import Categories.Category using (Category; _[_,_])

module Data.Sliced
  {o ℓ e}
  (C : Category o ℓ e)
  where

open import Categories.Functor using (Functor)
open import Categories.Category.Instance.Preds using (Preds)
open Category using (Obj; _∘_) renaming (id to ide)
open import Function using (id) renaming (_∘_ to _∘ᶠ_)
open import Level using (Level; _⊔_; suc; Lift; lower; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Unary using (Pred; _∈_; IUniversal; _⇒_)

CPred : (ℓ₁ : Level) → Set (o ⊔ suc ℓ₁)
CPred ℓ₁ = Pred (C .Obj) ℓ₁

private variable
  ℓ₁ : Level
  P Q : CPred ℓ₁
  d d₁ d₂ : C .Obj

infixl 15 _⇑_
infixl 14 _↑_
record _⇑_ (T : CPred ℓ₁) (domain : C .Obj) : Set (o ⊔ ℓ ⊔ ℓ₁) where
  constructor _↑_
  field
    { support } : C .Obj
    thing : T support
    thinning : C [ support , domain ]

map⇑ : ∀[ P ⇒ Q ] → ∀[ P ⇑_ ⇒ Q ⇑_ ]
map⇑ f (s ↑ θ) = f s ↑ θ

SlicedFunctor : Functor (Preds o (C .Obj)) (Preds (o ⊔ ℓ) (Lift ℓ (C .Obj)))
SlicedFunctor = record
  { F₀ = λ P d → P ⇑ lower d
  ; F₁ = λ f x → map⇑ f x
  ; identity = λ _ _ → refl
  ; homomorphism = λ _ _ → refl
  ; F-resp-≈ = λ {P} {Q} {α} {β} eq d (t ↑ θ) → cong (_↑ θ) (eq _ _)
  }

unit⇑ : ∀[ P ⇒ P ⇑_ ]
unit⇑ t = t ↑ C .ide

mult⇑ : ∀[ P ⇑_ ⇑_ ⇒ P ⇑_ ]
mult⇑ ((thing ↑ θ′) ↑ θ) = let _∘_ = C.(_∘_) in thing ↑ θ ∘ θ′

thin⇑ : C [ d₁ , d₂ ] → P ⇑ d₁ → P ⇑ d₂
thin⇑ θ x = mult⇑ (x ↑ θ)

-- TODO: ⇑ is a monad, also parametric in first argument
