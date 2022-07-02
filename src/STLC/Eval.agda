module STLC.Eval where

open import Codata.Sized.Delay using (Delay; later)
open import Codata.Sized.Delay.Effectful
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Effect.Monad using (RawMonad)
open import Level using (0ℓ)
open import Size using (Size)

open import STLC.TypedSyntax

private
  variable
    A : Set
    a : A
    as : List A
    Γ : Ctx
    t u : Ty

data All (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : P a → All P as → All P (a ∷ as)

⟦_⟧ : Ty → Set

Env : Ctx → Set
Env = All ⟦_⟧

data Closure (t u : Ty) : Set where
  closure : Exp u (t ∷ Γ) → Env Γ → Closure t u

⟦ unit ⟧ = ⊤
⟦ t ⟶ u ⟧ = Closure t u
⟦ nat ⟧ = ℕ

lookup : Env Γ → t ∈ Γ → ⟦ t ⟧
lookup (p ∷ _) here = p
lookup (_ ∷ η) (there x) = lookup η x

module _ {i : Size} where

  -- Reader over Delay
  M : Ctx → Set → Set
  M Γ x = Env Γ → Delay x i

  open RawMonad (Sequential.monad {i} {0ℓ})

  {-# TERMINATING #-}
  eval : Exp t Γ → M Γ ⟦ t ⟧

  eval-nat-elim : ℕ → Exp t Γ → Exp (t ⟶ t) Γ → M Γ ⟦ t ⟧
  eval-nat-elim 0 base _ η = eval base η
  eval-nat-elim (suc n) base ind η = eval-nat-elim n (app ind base) ind η

  eval tt η = return tt
  eval zero η = return 0
  eval (suc e) η = do
    n ← eval e η
    return (suc n)
  eval (nat-elim e base ind) η = do
    n ← eval e η
    eval-nat-elim n base ind η
  eval (var x) η = return (lookup η x)
  eval (fun e) η = return (closure e η)
  eval (app f e) η = do
    closure e′ η′ ← eval f η
    v ← eval e η
    eval e′ (v ∷ η′)
