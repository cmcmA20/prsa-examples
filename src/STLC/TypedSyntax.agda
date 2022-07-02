module STLC.TypedSyntax where

open import Data.List using (List; _∷_)

data Ty : Set where
  unit : Ty
  nat : Ty
  _⟶_ : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty

private
  variable
    A : Set
    a a₁ a₂ : A
    as : List A
    Γ : Ctx
    t u : Ty

data _∈_ : A → List A → Set where
  here : a ∈ (a ∷ as)
  there : a₁ ∈ as → a₁ ∈ (a₂ ∷ as)

data Exp : Ty → Ctx → Set where
  tt : Exp unit Γ

  zero : Exp nat Γ
  suc : Exp nat Γ → Exp nat Γ
  nat-elim : Exp nat Γ → Exp t Γ → Exp (t ⟶ t) Γ → Exp t Γ

  var : t ∈ Γ → Exp t Γ
  fun : Exp t (u ∷ Γ) → Exp (u ⟶ t) Γ
  app : Exp (t ⟶ u) Γ → Exp t Γ → Exp u Γ
