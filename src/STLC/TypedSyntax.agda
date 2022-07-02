{-# OPTIONS --safe --no-sized-types --no-guardedness --no-subtyping #-}
module STLC.TypedSyntax where

open import Data.Bwd using (Bwd; _-,_; _∈_)
open import Level using (0ℓ)

data Ty : Set where
  unit : Ty
  nat : Ty
  _⟶_ : Ty → Ty → Ty

open import Data.Scoped {0ℓ} Ty public hiding (var)

Ctx : Set
Ctx = Bwd Ty

private
  variable
    A : Set
    a a′ : A
    as : Bwd A
    Γ : Ctx
    t u : Ty

data Exp : Ty → Scoped 0ℓ where
  tt : Exp unit Γ

  zero : Exp nat Γ
  suc : Exp nat Γ → Exp nat Γ
  nat-elim : Exp nat Γ → Exp t Γ → Exp (t ⟶ t) Γ → Exp t Γ

  var : t ∈ Γ → Exp t Γ
  fun : Exp t (Γ -, u) → Exp (u ⟶ t) Γ
  app : Exp (t ⟶ u) Γ → Exp t Γ → Exp u Γ
