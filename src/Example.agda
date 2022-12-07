module Example where

open import Level using (0ℓ)
open import Data.Bool using (false; true; _∧_) renaming (Bool to 𝔹)
open import Data.Nat using (ℕ)

data Ty : Set where
  Unit  :           Ty
  -- Bool  :           Ty
  Nat   :           Ty
  _*_   : Ty → Ty → Ty
  _⟶_  : Ty → Ty → Ty
  -- IOTok :           Ty
infixr 6 _*_ _⟶_

open import Data.Scoped Ty

data Tm : Ty → Scoped 0ℓ where
  # : {R : Ty} → ∀[ Vaᵣ R ⇒ Tm R ]

  unit : ∀[ Tm Unit ]

  -- tt ff     : ∀[ Tm Bool ]
  -- bool-elim : {R : Ty} → ∀[ Tm Bool ×ᵣ Tm R ×ᵣ Tm R ⇒ Tm R ]

  zero     : ∀[ Tm Nat ]
  suc      : ∀[ Tm Nat ⇒ Tm Nat ]
  nat-elim : {R : Ty} → ∀[ Tm Nat ×ᵣ Tm R ×ᵣ Tm (R ⟶ R) ⇒ Tm R ]

  pair      : {T₁ T₂ : Ty} → ∀[ Tm T₁ ×ᵣ Tm T₂ ⇒ Tm (T₁ * T₂) ]
  pair-elim : {T₁ T₂ R : Ty} → ∀[ Tm (T₁ * T₂) ×ᵣ Tm (T₁ ⟶ T₂ ⟶ R) ⇒ Tm R ]

  ƛ_  : {T R : Ty} → ∀[ (([] -, T) ⊢ Tm R) ⇒ Tm (T ⟶ R) ]
  $ : {T R : Ty} → ∀[ Tm (T ⟶ R) ×ᵣ Tm T ⇒ Tm R ]

  -- readNat : ∀[ Tm IOTok ⇒ Tm (Nat * IOTok) ]
  -- print   : {T : Ty} → ∀[ Tm T ×ᵣ Tm IOTok ⇒ Tm IOTok ]
  -- halt    : ∀[ Tm IOTok ⇒ Tm Unit ]


infix 0 _is-linear-in_
_is-linear-in_ : {Γ : Bwd Ty} {R : Ty} (term : Tm R Γ) {Ι : Bwd Ty} (θ : Ι ⊑ Γ) → 𝔹
_is-linear-in_ = {!!}
