{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
module Data.Substructure where

open import Categories.Category using (Category)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Binary using (Antisymmetric; Poset; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (refl)

data Substructure : Set where Ordered Linear Relevant Unrestricted : Substructure

_≈_ : (s₁ s₂ : Substructure) → Set
_≈_ Ordered Ordered = ⊤
_≈_ Linear Linear = ⊤
_≈_ Relevant Relevant = ⊤
_≈_ Unrestricted Unrestricted = ⊤
_≈_ _ _ = ⊥

eq-refl : Reflexive _≈_
eq-refl {Ordered} = tt
eq-refl {Linear} = tt
eq-refl {Relevant} = tt
eq-refl {Unrestricted} = tt

eq-sym : Symmetric _≈_
eq-sym {Ordered} {Ordered} _ = tt
eq-sym {Linear} {Linear} _ = tt
eq-sym {Relevant} {Relevant} _ = tt
eq-sym {Unrestricted} {Unrestricted} _ = tt

eq-trans : Transitive _≈_
eq-trans {Ordered} {Ordered} {Ordered} _ _ = tt
eq-trans {Linear} {Linear} {Linear} _ _ = tt
eq-trans {Relevant} {Relevant} {Relevant} _ _ = tt
eq-trans {Unrestricted} {Unrestricted} {Unrestricted} _ _ = tt

_≤_ : (s₁ s₂ : Substructure) → Set
_≤_ Ordered _ = ⊤
_≤_ Linear Ordered = ⊥
_≤_ Linear _ = ⊤
_≤_ Relevant Ordered = ⊥
_≤_ Relevant Linear = ⊥
_≤_ Relevant _ = ⊤
_≤_ Unrestricted Unrestricted = ⊤
_≤_ _ _ = ⊥

ord-refl : {s₁ s₂ : Substructure} → s₁ ≈ s₂ → s₁ ≤ s₂
ord-refl {Ordered} {Ordered} _ = tt
ord-refl {Linear} {Linear} _ = tt
ord-refl {Relevant} {Relevant} _ = tt
ord-refl {Unrestricted} {Unrestricted} _ = tt

ord-trans : Transitive _≤_
ord-trans {Ordered} {_} {_} _ _ = tt
ord-trans {Linear} {Linear} {Linear} _ _ = tt
ord-trans {Linear} {Linear} {Relevant} _ _ = tt
ord-trans {Linear} {Linear} {Unrestricted} _ _ = tt
ord-trans {Linear} {Relevant} {Relevant} _ _ = tt
ord-trans {Linear} {Relevant} {Unrestricted} _ _ = tt
ord-trans {Linear} {Unrestricted} {Unrestricted} _ _ = tt
ord-trans {Relevant} {Relevant} {Relevant} _ _ = tt
ord-trans {Relevant} {Relevant} {Unrestricted} _ _ = tt
ord-trans {Relevant} {Unrestricted} {Unrestricted} _ _ = tt
ord-trans {Unrestricted} {Unrestricted} {Unrestricted} _ _ = tt

eq-ord-antisym : Antisymmetric _≈_ _≤_
eq-ord-antisym {Ordered} {Ordered} _ _ = tt
eq-ord-antisym {Linear} {Linear} _ _ = tt
eq-ord-antisym {Relevant} {Relevant} _ _ = tt
eq-ord-antisym {Unrestricted} {Unrestricted} _ _ = tt

SubstructurePoset : Poset 0ℓ 0ℓ 0ℓ
SubstructurePoset = record
  { Carrier = Substructure
  ; _≈_ = _≈_
  ; _≤_ = _≤_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = record
        { refl = eq-refl
        ; sym = eq-sym
        ; trans = eq-trans
        }
      ; reflexive = ord-refl
      ; trans = ord-trans
      }
    ; antisym = eq-ord-antisym
    }
  }

SubstructureCat : Category _ _ _
SubstructureCat = Thin where open import Categories.Category.Construction.Thin 0ℓ SubstructurePoset
