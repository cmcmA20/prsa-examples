module STLC.Eval where

open import Codata.Sized.Delay using (Delay)
open import Codata.Sized.Delay.Effectful
open import Data.Bool using (Bool)
open import Data.Bwd using (Bwd; []; _-,_)
open import Data.Nat using (ℕ; suc)
-- open import Data.Scoped
open import Data.Unit using (⊤; tt)
open import Effect.Monad using (RawMonad)
open import Level using (0ℓ)
open import Size using (Size)

open import STLC.TypedSyntax

private
  variable
    A : Set
    a : A
    as : Bwd A
    Γ : Ctx
    t u : Ty

data All (P : A → Set) : Bwd A → Set where
  [] : All P []
  _-,_ : All P as → P a → All P (as -, a)

Env : Ctx → Set

data ⟦_⟧ : Ty → Set where
  ttᵥ : ⟦ unit ⟧
  closure : Exp u (Γ -, t) → Env Γ → ⟦ t ⟶ u ⟧
  ⟦_⟧ᵥ : ℕ → ⟦ nat ⟧

Env = All ⟦_⟧

lookup : Env Γ → t ∈ Γ → ⟦ t ⟧
lookup (_ -, p) here = p
lookup (η -, _) (there x) = lookup η x

module _ {i : Size} where

  -- Reader over Delay
  M : Ctx → Set → Set
  M Γ A = Env Γ → Delay A i

  open RawMonad (Sequential.monad {i} {0ℓ})

  {-# TERMINATING #-}
  eval : Exp t Γ → M Γ ⟦ t ⟧

  eval-nat-elim : ℕ → Exp t Γ → Exp (t ⟶ t) Γ → M Γ ⟦ t ⟧
  eval-nat-elim 0 base _ η = eval base η
  eval-nat-elim (suc n) base ind η = eval-nat-elim n (app ind base) ind η

  eval tt η = return ttᵥ
  eval zero η = return ⟦ 0 ⟧ᵥ
  eval (suc e) η = do
    ⟦ n ⟧ᵥ ← eval e η
    return ⟦ suc n ⟧ᵥ
  eval (nat-elim e base ind) η = do
    ⟦ n ⟧ᵥ ← eval e η
    eval-nat-elim n base ind η
  eval (var x) η = return (lookup η x)
  eval (fun e) η = return (closure e η)
  eval (app f e) η = do
    closure e′ η′ ← eval f η
    v ← eval e η
    eval e′ (η′ -, v)
