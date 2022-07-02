open import Categories.Category using (Category; _[_,_])

module Data.Sliced
  {o ℓ e}
  (C : Category o ℓ e)
  where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Categories.Functor using (Functor)
open Category using (Obj; _∘_) renaming (id to ide)
open import Function.Base using (id) renaming (_∘_ to _∘ᶠ_)
open import Level using (Level; _⊔_; suc; Lift; lift; lower; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; _∈_; IUniversal; _⇒_)

-- TODO finish this
Preds : ∀ o → Set o → Category (suc o) o o
Preds o A = record
  { Obj = Pred A o
  ; _⇒_ = λ P Q → ∀[ P ⇒ Q ]
  ; _≈_ = λ {P Q} f g → (x : A) → (y : P x) → f y ≡ g y -- is it true?
  ; id = id
  ; _∘_ = λ α β → α ∘ᶠ β
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }

CPred : (ℓ₁ : Level) → Set (o ⊔ suc ℓ₁)
CPred ℓ₁ = Pred (C .Obj) ℓ₁

infixl 15 _⇑_
infixl 14 _↑_
record _⇑_ {ℓ₁} (T : CPred ℓ₁) (domain : C .Obj) : Set (o ⊔ ℓ ⊔ ℓ₁) where
  constructor _↑_
  field
    { support } : C .Obj
    thing : T support
    thinning : C [ support , domain ]

map : ∀ {ℓ₁} → {P Q : CPred ℓ₁} → ∀[ P ⇒ Q ] → ∀[ P ⇑_ ⇒ Q ⇑_ ]
map f (s ↑ θ) = f s ↑ θ

map-id : ∀ {ℓ₁} → {P : CPred ℓ₁} → {d : C .Obj} → (t : P ⇑ d) → map id t ≡ t
map-id (thing ↑ thinning) = refl

-- TODO finish this
module _ {ℓ₁ ℓ₂} {funExt : Extensionality ℓ₁ ℓ₂} where
  SlicedFunctor : Functor (Preds o (C .Obj)) (Preds (o ⊔ ℓ) (Lift ℓ (C .Obj)))
  SlicedFunctor = record
    { F₀ = λ P d → P ⇑ lower d
    ; F₁ = λ f x → map f x
    ; identity = λ _ → map-id
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!}
    }

unit : ∀ {ℓ₁} → {P : CPred ℓ₁} → ∀[ P ⇒ P ⇑_ ]
unit t = t ↑ C .ide

mult : ∀ {ℓ₁} → {P : CPred ℓ₁} → {d : C .Obj} → ∀[ P ⇑_ ⇑_ ⇒ P ⇑_ ]
mult ((thing ↑ θ′) ↑ θ) = let _∘_ = C.(_∘_) in thing ↑ θ ∘ θ′

thin : ∀ {ℓ₁} → {P : CPred ℓ₁} → {d₁ d₂ : C .Obj} → C [ d₁ , d₂ ] → P ⇑ d₁ → P ⇑ d₂
thin {d₂ = d₂} θ x = mult {d = d₂} (x ↑ θ)

-- TODO: ⇑ is a monad, also parametric in first argument
