{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
open import Categories.Category using (Category; _[_,_])

module Data.Sliced
  {ℓ e}
  (C : Category ℓ ℓ e)
  where

open import Categories.Category.Instance.Preds using (Preds)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Monad using (Monad)
open Category C using (Obj; _∘_; identityˡ; identityʳ; assoc; sym-assoc) renaming (id to ide)
open import Function using (id) renaming (_∘_ to _∘ᶠ_)
open import Level using (Level; _⊔_; suc; Lift; lower; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Unary using (Pred; _∈_; IUniversal; _⇒_)

CPred : (ℓ₁ : Level) → Set (ℓ ⊔ suc ℓ₁)
CPred ℓ₁ = Pred Obj ℓ₁

private variable
  ℓ₁ : Level
  P Q : CPred ℓ₁
  d d₁ d₂ : Obj

infixl 15 _⇑_
infixl 14 _↑_
record _⇑_ (T : CPred ℓ₁) (domain : Obj) : Set (ℓ ⊔ ℓ₁) where
  constructor _↑_
  field
    { support } : Obj
    thing : T support
    thinning : C [ support , domain ]

map⇑ : ∀[ P ⇒ Q ] → ∀[ P ⇑_ ⇒ Q ⇑_ ]
map⇑ f (s ↑ θ) = f s ↑ θ

SlicedFunctor : Endofunctor (Preds ℓ Obj)
SlicedFunctor = record
  { F₀ = λ P d → P ⇑ d
  ; F₁ = λ f x → map⇑ f x
  ; identity = λ _ _ → refl
  ; homomorphism = λ _ _ → refl
  ; F-resp-≈ = λ eq _ (_ ↑ θ) → cong (_↑ θ) (eq _ _)
  }

unit⇑ : ∀[ P ⇒ P ⇑_ ]
unit⇑ t = t ↑ ide

mult⇑ : ∀[ P ⇑_ ⇑_ ⇒ P ⇑_ ]
mult⇑ ((thing ↑ θ′) ↑ θ) = thing ↑ (θ ∘ θ′)

thin⇑ : C [ d₁ , d₂ ] → P ⇑ d₁ → P ⇑ d₂
thin⇑ θ x = mult⇑ (x ↑ θ)


-- SlicedMonad : Monad (Preds ℓ Obj)
-- SlicedMonad = record
--   { F = SlicedFunctor
--   ; η = record
--     { η = λ _ → unit⇑
--     ; commute = λ _ _ _ → refl
--     ; sym-commute = λ _ _ _ → refl
--     }
--   ; μ = record
--     { η = λ _ → mult⇑
--     ; commute = λ _ _ _ → refl
--     ; sym-commute = λ _ _ _ → refl
--     }
--   ; assoc = λ x (((y ↑ ψ) ↑ ϕ) ↑ θ) → cong (y ↑_) {!!}
--   ; sym-assoc = {!!}
--   ; identityˡ = λ x (y ↑ θ) → cong (y ↑_) {!!}
--   ; identityʳ = {!!}
--   }

-- -- TODO: parametric in first argument
