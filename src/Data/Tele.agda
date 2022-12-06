{-# OPTIONS --safe #-}
open import Level using (Level; _⊔_; 0ℓ)

module Data.Tele
  {ℓ : Level}
  (𝐾 : Set ℓ)
  where

open import Data.Bwd
open import Data.Scoped 𝐾
open import Data.Substructure
open import Data.Product
open import Relation.Unary using (IUniversal; _⇒_; _∈_)

private variable
  scope : Bwd 𝐾
  k : 𝐾

data Tele (T : Scoped ℓ) : Bwd 𝐾 → Set ℓ where
  [] : Tele T scope
  _-,_ : T scope → Tele T (scope -, k) → Tele T scope

data Teleₛ (T : Scoped ℓ) : Substructure × Bwd 𝐾 → Set ℓ where
  []ₛ : ∀[ Oneₛ ↾ ⇒ Teleₛ T ]
  _-,ₛ_ : ∀[ T ↾ ×ₛₛ ([] -, k) ⊢ₛ Teleₛ T ⇒ Teleₛ T ]

data Lamₛ : Substructure × Bwd 𝐾 → Set ℓ where
  v : ∀[ Vaₛ k ⇒ Lamₛ ]
  app : ∀[ Lamₛ ×ₛₛ Lamₛ ⇒ Lamₛ ]
  lam : ∀[ ([] -, k) ⊢ₛ Lamₛ ⇒ Lamₛ ]

lamₛ : ∀[ Unrestricted ⇃ Lamₛ ⇒ Relevant ⇃ (Lamₛ ⇑ₛ_) ]
lamₛ (v only) = map⇑ₛ v (vaₛ (oz os))
lamₛ (app (pair (f ↑ ψ) (s ↑ ξ) _)) =
  let
    f′ ↑ₛ (s₁ , θ) = lamₛ f
    s′ ↑ₛ (s₂ , ϕ) = lamₛ s
    _ , ψ′ , θ′ , ϕ′ , _ , (c ↑′ z) , _ = (θ ⋆ ψ) ∐ (ϕ ⋆ ξ)
    zz = f′
  in map⇑ₛ app (pair {!thin⇑′ ? ?!} ({!!} ↑ ϕ′) (c ↑′ z) ↑ₛ (si {Relevant} , ψ′))
lamₛ (lam (θ ⑊ e)) with lamₛ e
... | q ↑ (w , z) = map⇑ₛ lam (_ ⑊ₛₛ (q ↑ₛ (w , z ⋆ (oi ⧺⊑ θ))))

-- lamₛ (v only) = map⇑ v (vaᵣ oi)
-- lamₛ (app e) = let zz = outlₛ {Lamₛ} {Lamₛ} {(Unrestricted , {!!})} in {!!}
-- lamₛ (lam x) = {!!}
