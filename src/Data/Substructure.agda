{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
module Data.Substructure where

open import Categories.Category using (Category)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Binary using (Antisymmetric; Poset; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (refl)

data Substructure : Set where Ordered Linear Relevant Unrestricted : Substructure

eq : (s₁ s₂ : Substructure) → Set
eq Ordered Ordered = ⊤
eq Linear Linear = ⊤
eq Relevant Relevant = ⊤
eq Unrestricted Unrestricted = ⊤
eq _ _ = ⊥

eq-refl : Reflexive eq
eq-refl {Ordered} = tt
eq-refl {Linear} = tt
eq-refl {Relevant} = tt
eq-refl {Unrestricted} = tt

eq-sym : Symmetric eq
eq-sym {Ordered} {Ordered} _ = tt
eq-sym {Linear} {Linear} _ = tt
eq-sym {Relevant} {Relevant} _ = tt
eq-sym {Unrestricted} {Unrestricted} _ = tt

eq-trans : Transitive eq
eq-trans {Ordered} {Ordered} {Ordered} _ _ = tt
eq-trans {Linear} {Linear} {Linear} _ _ = tt
eq-trans {Relevant} {Relevant} {Relevant} _ _ = tt
eq-trans {Unrestricted} {Unrestricted} {Unrestricted} _ _ = tt

ord : (s₁ s₂ : Substructure) → Set
ord Ordered _ = ⊤
ord Linear Ordered = ⊥
ord Linear _ = ⊤
ord Relevant Ordered = ⊥
ord Relevant Linear = ⊥
ord Relevant _ = ⊤
ord Unrestricted Unrestricted = ⊤
ord _ _ = ⊥

ord-refl : {s₁ s₂ : Substructure} → eq s₁ s₂ → ord s₁ s₂
ord-refl {Ordered} {Ordered} _ = tt
ord-refl {Linear} {Linear} _ = tt
ord-refl {Relevant} {Relevant} _ = tt
ord-refl {Unrestricted} {Unrestricted} _ = tt

ord-trans : Transitive ord
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

eq-ord-antisym : Antisymmetric eq ord
eq-ord-antisym {Ordered} {Ordered} _ _ = tt
eq-ord-antisym {Linear} {Linear} _ _ = tt
eq-ord-antisym {Relevant} {Relevant} _ _ = tt
eq-ord-antisym {Unrestricted} {Unrestricted} _ _ = tt

SubstructurePoset : Poset 0ℓ 0ℓ 0ℓ
SubstructurePoset = record
  { Carrier = Substructure
  ; _≈_ = eq
  ; _≤_ = ord
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
