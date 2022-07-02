module STLC.TypedSyntax where

open import Data.Bwd using (Bwd; _-,_)

data Ty : Set where
  unit : Ty
  nat : Ty
  _⟶_ : Ty → Ty → Ty

Ctx : Set
Ctx = Bwd Ty

private
  variable
    A : Set
    a a′ : A
    as : Bwd A
    Γ : Ctx
    t u : Ty

data _∈_ : A → Bwd A → Set where
  here : a ∈ (as -, a)
  there : a ∈ as → a ∈ (as -, a′)

data Exp : Ty → Ctx → Set where
  tt : Exp unit Γ

  zero : Exp nat Γ
  suc : Exp nat Γ → Exp nat Γ
  nat-elim : Exp nat Γ → Exp t Γ → Exp (t ⟶ t) Γ → Exp t Γ

  var : t ∈ Γ → Exp t Γ
  fun : Exp t (Γ -, u) → Exp (u ⟶ t) Γ
  app : Exp (t ⟶ u) Γ → Exp t Γ → Exp u Γ
