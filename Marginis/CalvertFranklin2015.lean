import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.RingTheory.Regular.RegularSequence

/- This concerns the second sentence in the Introduction in the paper
Genericity and UD–random reals by WESLEY CALVERT, JOHANNA N.Y. FRANKLIN.
We define uniform distribution and prove that the constant 0 sequence is not uniformly distributed.
-/

open Finset

variable (x : ℕ → Set.Ico (0:ℝ) 1)
variable (n:ℕ)
variable (i : Fin n)
variable (a b:ℝ)

def uniformly_distributed (x : ℕ → Set.Ico (0:ℝ) 1) :=
  ∀ a b ε : ℝ, 0 ≤ a → a < b → b ≤ 1 → ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    abs (card (filter (λ i : Fin n ↦ a < x i ∧ x i < b) univ) - (b - a) * n) < n * ε

example : ¬ uniformly_distributed (λ _ ↦ ⟨0,by simp⟩) := by
  unfold uniformly_distributed
  push_neg
  use (1:ℝ)/2;use (1:ℝ);use (1:ℝ)/2
  constructor;aesop;constructor;exact one_half_lt_one
  constructor;rfl;constructor;aesop
  intro n₀;use n₀
  constructor;rfl;simp
  split_ifs with h
  . exfalso;contrapose h;simp
  . simp;ring_nf;apply @le_abs_self ℝ
