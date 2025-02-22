import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Notation

/-!

## Abraham Robinson (6 October 1918 - 11 April 1974)

[EDITORS, Journal of Logic & Analysis](http://logicandanalysis.org/index.php/jla/article/view/350)

This paper is a reminiscence of Abraham Robinson.

We include here a formalization of
the ordering of a countable nonstandard model of `Th(N,<)`,
which looks like `ℕ ⊕ (ℚ × ℤ)`.
-/

/-- The underlying set of a countable nonstandard model of `Th(N,<)`. -/
def N := ℕ ⊕ (ℚ × ℤ)

/-- Comparing an element of `N` with a standard element of `N`. -/
def nat_lt (n:ℕ) : N → Prop
| (Sum.inl m) => n < m
| (Sum.inr _)  => True

/-- Comparing an element of `N` with a nonstandard element of `N`. -/
def inf_lt (q₁:ℚ) (z₁:ℤ) : N → Prop
| (Sum.inl _) => False
| (Sum.inr (q₂,z₂))  => q₁ < q₂ ∨ (q₁ = q₂ ∧ (z₁ < z₂))

/-- The ordering of a countable nonstandard model of `Th(N,<)`. -/
def lt : N → N → Prop
| (Sum.inl n) => nat_lt n
| (Sum.inr (q,z))  => inf_lt q z

/-- The natural number 3 is less than the infinite number (0,2). -/
lemma lt_example₁: lt (Sum.inl 3) (Sum.inr (0,2)) := by
  unfold lt nat_lt
  simp

/-- The natural number 3 is not greater than the infinite number (0,2). -/
lemma lt_example₂ : ¬ lt (Sum.inr (0,2)) (Sum.inl 3) := by
  unfold lt inf_lt
  simp
