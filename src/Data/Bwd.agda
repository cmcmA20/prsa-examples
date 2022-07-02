{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
module Data.Bwd where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)
open import Function.Base using (_|>_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

infixl 17 _-,_
data Bwd {ℓ : Level} (A : Set ℓ) : Set ℓ where
  [] : Bwd A
  _-,_ : Bwd A → A → Bwd A

map : ∀ {ℓ} → {A B : Set ℓ} → (A → B) → Bwd A → Bwd B
map f [] = []
map f (xs -, x) = map f xs -, f x

map-id : ∀ {ℓ} → {A : Set ℓ} → (xs : Bwd A) → map (λ a → a) xs ≡ xs
map-id [] = refl
map-id (xs -, x) = map-id xs |> cong (_-, x)

map-comp : ∀ {ℓ} → {A B C : Set ℓ} → (f : A → B) → (g : B → C) → (xs : Bwd A) → map (λ a → g (f a)) xs ≡ map g (map f xs)
map-comp _ _ [] = refl
map-comp f g (xs -, x) = map-comp f g xs |> cong (_-, g (f x))

infixl 6 _⧺_
_⧺_ : ∀ {ℓ} → {A : Set ℓ} → Bwd A → Bwd A → Bwd A
xs ⧺ [] = xs
xs ⧺ (ys -, y) = (xs ⧺ ys) -, y

module _ {funExt : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂} where
  BwdFunctor : ∀ {ℓ} → Functor (Sets ℓ) (Sets ℓ)
  Functor.F₀ BwdFunctor = Bwd
  Functor.F₁ BwdFunctor = map
  Functor.identity BwdFunctor = map-id _
  Functor.homomorphism BwdFunctor = map-comp _ _ _
  Functor.F-resp-≈ BwdFunctor p = cong (λ h → map h _) (funExt λ _ → p)
