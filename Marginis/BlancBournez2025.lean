import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## Simulation of Turing machines with analytic discrete ODEs: Polynomial-time and space over the reals characterised with discrete ordinary differential equations
Manon Blanc, Olivier Bournez

Code by ChatGPT.
-/

-- Define the discrete derivative operator on functions from ℤ to ℤ
def discrete_derivative₁ (f : ℤ → ℤ) : ℤ → ℤ :=
  λ x => f (x + 1) - f x

-- More general version using type classes
variable {α : Type*} [AddGroup α]

def discrete_derivative₂ (f : ℤ → α) : ℤ → α :=
  λ x => f (x + 1) - f x
