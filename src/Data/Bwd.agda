{-# OPTIONS --safe #-}
module Data.Bwd where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Functor)
open import Function using (_|>_; _∘_; id)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Unary using (Pred)

private variable
  ℓ ℓ₁ : Level

infixl 17 _-,_
data Bwd (A : Set ℓ) : Set ℓ where
  [] : Bwd A
  _-,_ : Bwd A → A → Bwd A

private variable
  A B C : Set ℓ

infixl 6 _++_
_++_ : Bwd A → Bwd A → Bwd A
xs ++ [] = xs
xs ++ (ys -, y) = (xs ++ ys) -, y

data Any {A : Set ℓ} (P : Pred A ℓ₁) : Pred (Bwd A) ℓ₁ where
  here  : ∀ {x xs} (px  : P x) → Any P (xs -, x)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (xs -, x)

infix 4 _∈_
_∈_ : A → Bwd A → Set _
x ∈ xs = Any (_≡ x) xs

-- contravariant functor from Δ₊ to Sets?
-- data All {A : Set ℓ} (P : Pred A ℓ₁) : Pred (Bwd A) ℓ₁ where
--   [] : ∀ {xs} → All P xs
--   _::_ : ∀ {x xs} → All P xs → P x → All P (xs -, x)

module Category where
  map : (A → B) → Bwd A → Bwd B
  map f [] = []
  map f (xs -, x) = map f xs -, f x

  map-id : (xs : Bwd A) → map id xs ≡ xs
  map-id [] = refl
  map-id (xs -, x) = map-id xs |> cong (_-, x)

  map-comp : (f : A → B) → (g : B → C) → (xs : Bwd A) → map (g ∘ f) xs ≡ map g (map f xs)
  map-comp _ _ [] = refl
  map-comp f g (xs -, x) = map-comp f g xs |> cong (_-, g (f x))

  module _ {funExt : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂} where
    BwdFunctor : Functor (Sets ℓ) (Sets ℓ)
    Functor.F₀ BwdFunctor = Bwd
    Functor.F₁ BwdFunctor = map
    Functor.identity BwdFunctor = map-id _
    Functor.homomorphism BwdFunctor = map-comp _ _ _
    Functor.F-resp-≈ BwdFunctor p = cong (λ h → map h _) (funExt λ _ → p)
