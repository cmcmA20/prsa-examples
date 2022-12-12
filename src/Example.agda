module Example where

open import Data.Bool using (false; true; _∧_) renaming (Bool to 𝔹)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Level using (0ℓ)

data Ty : Set where
  Unit  :           Ty
  -- Bool  :           Ty
  Nat   :           Ty
  _*_   : Ty → Ty → Ty
  _⟶_  : Ty → Ty → Ty
  -- IOTok :           Ty
infixr 6 _*_ _⟶_

open import Data.Scoped Ty

private
  variable
    Γ : Bwd Ty
    R T T₁ T₂ : Ty

data Expr : Ty → Scoped 0ℓ where
  # : (x : R ⟵ Γ) → Expr R Γ

  unit : Expr Unit Γ

  zero     :                                           Expr Nat Γ
  suc      : Expr Nat Γ                              → Expr Nat Γ
  nat-elim : Expr Nat Γ × Expr R Γ × Expr (R ⟶ R) Γ → Expr R Γ

  tuple      : Expr T₁ Γ        × Expr T₂ Γ              → Expr (T₁ * T₂) Γ
  tuple-elim : Expr (T₁ * T₂) Γ × Expr (T₁ ⟶ T₂ ⟶ R) Γ → Expr R Γ

  ƛ_ : Expr R (Γ -, T)            → Expr (T ⟶ R) Γ
  $  : Expr (T ⟶ R) Γ × Expr T Γ → Expr R Γ

data Tm : Ty → Scoped 0ℓ where
  # : ∀[ Vaᵣ R ⇒ Tm R ]

  unit : ∀[ Oneᵣ ⇒ Tm Unit ]

  -- tt ff     : ∀[ Oneᵣ => Tm Bool ]
  -- bool-elim : ∀[ Tm Bool ×ᵣ Tm R ×ᵣ Tm R ⇒ Tm R ]

  zero     : ∀[ Oneᵣ                          ⇒ Tm Nat ]
  suc      : ∀[ Tm Nat                        ⇒ Tm Nat ]
  nat-elim : ∀[ Tm Nat ×ᵣ Tm R ×ᵣ Tm (R ⟶ R) ⇒ Tm R   ]

  tuple      : ∀[ Tm T₁        ×ᵣ Tm T₂              ⇒ Tm (T₁ * T₂) ]
  tuple-elim : ∀[ Tm (T₁ * T₂) ×ᵣ Tm (T₁ ⟶ T₂ ⟶ R) ⇒ Tm R         ]

  ƛ_ : ∀[ (([] -, T) ⊢ Tm R)  ⇒ Tm (T ⟶ R) ]
  $  : ∀[ Tm (T ⟶ R) ×ᵣ Tm T ⇒ Tm R        ]

  -- readNat : ∀[ Tm IOTok ⇒ Tm (Nat * IOTok) ]
  -- print   : {T : Ty} → ∀[ Tm T ×ᵣ Tm IOTok ⇒ Tm IOTok ]
  -- halt    : ∀[ Tm IOTok ⇒ Tm Unit ]

translateᵣ : ∀[ Expr T ⇒ Tm T ⇑_ ]
translateᵣ (# x) = map⇑ # (vaᵣ x)
translateᵣ unit = map⇑ unit ⟨⟩ᵣ
translateᵣ zero = map⇑ zero ⟨⟩ᵣ
translateᵣ (suc n) = map⇑ suc (translateᵣ n)
translateᵣ (nat-elim (n , z , s)) = map⇑ nat-elim (translateᵣ n ,ᵣ translateᵣ z ,ᵣ translateᵣ s)
translateᵣ (tuple (t₁ , t₂)) = map⇑ tuple (translateᵣ t₁ ,ᵣ translateᵣ t₂)
translateᵣ (tuple-elim (p , pe)) = map⇑ tuple-elim (translateᵣ p ,ᵣ translateᵣ pe)
translateᵣ (ƛ t) = map⇑ ƛ_ (_ ⑊ᵣ translateᵣ t)
translateᵣ ($ (rator , rand)) = map⇑ $ (translateᵣ rator ,ᵣ translateᵣ rand)

_never-drops_ : {support : Bwd Ty} (θ : support ⊑ Γ) {Ι : Bwd Ty} (ψ : Ι ⊑ Γ) → 𝔹
_      never-drops oz     = true
(θ o′) never-drops (ψ o′) = θ never-drops ψ
(θ os) never-drops (ψ o′) = θ never-drops ψ
(θ o′) never-drops (ψ os) = false
(θ os) never-drops (ψ os) = θ never-drops ψ

-- $
-- (pair
--  ((ƛ
--    ((oz os) ⑊
--     $
--     (pair (# only ↑ ((oz os) o′)) (# only ↑ ((oz o′) os))
--      ((czz cs′) c′s))))
--   ↑ (oz os))
--  (zero ⟨⟩ ↑ (oz o′)) (czz cs′))
-- ↑ (oz os)

mutual
  infix 0 _is-pair-linear-in_
  _is-pair-linear-in_ : (p : (Tm T₁ ×ᵣ Tm T₂) Γ) {Ι : Bwd Ty} (ψ : Ι ⊑ Γ) → 𝔹
  pair outl outr c is-pair-linear-in ψ with subCop ψ c
  ... | ! ! ! ! (ψₗ , ψᵣ , _) = (c linearly-covers ψ) ∧ (outl is-linearly-scoped-in (ψₗ ⋆ outl .thinning)) ∧ (outr is-linearly-scoped-in (ψᵣ ⋆ outr .thinning))

  infix 0 _is-linear-in_
  _is-linear-in_ : (term : Tm R Γ) {Ι : Bwd Ty} (ψ : Ι ⊑ Γ) → 𝔹
  # only is-linear-in _ = true
  unit ⟨⟩ is-linear-in _ = true
  zero ⟨⟩ is-linear-in _ = true
  suc n is-linear-in ψ = n is-linear-in ψ
  nat-elim (pair outl outr c) is-linear-in ψ = {!!} ∧ outr is-linearly-scoped-in ψ ∧ (c linearly-covers ψ)
  tuple p is-linear-in ψ = p is-pair-linear-in ψ
  tuple-elim p is-linear-in ψ = p is-pair-linear-in ψ
  ƛ ((oz os) ⑊ t) is-linear-in ψ = t is-linear-in (ψ ++⊑ oi) -- FIXME now we're always checking linearity of lambda argument
  ƛ ((oz o′) ⑊ _) is-linear-in _ = false
  $ p is-linear-in ψ = p is-pair-linear-in ψ

  _is-linearly-scoped-in_ : (t′ : Tm R ⇑ Γ) {Ι : Bwd Ty} (ψ : Ι ⊑ Γ) → 𝔹
  (t ↑ θ) is-linearly-scoped-in ψ = let ! (ψ′ , _) = θ ∏ ψ in θ never-drops ψ ∧ (t is-linear-in ψ′)

_is-linear : Expr T Γ → 𝔹
e is-linear = (translateᵣ e) is-linearly-scoped-in oi

module Test where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  
  I : (Γ : Bwd Ty) (T : Ty) → Expr (T ⟶ T) Γ
  I _ _ = ƛ # (oe os)

  _ : I [] T is-linear ≡ true
  _ = refl

  K : (Γ : Bwd Ty) (R T : Ty) → Expr (R ⟶ T ⟶ R) Γ
  K _ _ _ = ƛ (ƛ # (oe os o′))

  _ : K [] R T is-linear ≡ false
  _ = refl

  contrived₁ : Expr Nat ([] -, Nat)
  contrived₁ = $ (I _ _ , zero)

  _ : contrived₁ is-linear ≡ false
  _ = refl

  contrived₂ : Expr Nat ([] -, (Nat ⟶ Nat))
  contrived₂ = $ ((ƛ $ (# (oz os o′) , # (oz o′ os))) , ($ ((# (oz os)) , zero)))

  _ : contrived₂ is-linear ≡ false
  _ = refl

  contrived₃ : Expr Nat ([] -, (Nat ⟶ Nat))
  contrived₃ = $ ((ƛ $ (# (oz os o′) , # (oz o′ os))) , zero)

  _ : contrived₃ is-linear ≡ true
  _ = refl
