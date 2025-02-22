import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

/-!

# A computational study of a class of recursive inequalities

[MORENIKEJI NERI and THOMAS POWELL](http://logicandanalysis.org/index.php/jla/article/view/469)

We formalize the first example from the paper.
-/

lemma firstExampleNeri (μ : ℕ → NNReal) (c : Set.Ico (0:ℝ) 1)
  (h : ∀ n, μ (n + 1) ≤ c.1 * μ n) (n : ℕ):
  μ n ≤ c.1^n * μ 0 := by
  induction n with
  |zero => simp only [pow_zero, one_mul, le_refl]
  |succ n hn =>
    calc
    _ ≤ c.1 * μ n := h n
    _ ≤ _ := by
      ring_nf;
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hn c.2.1

/--
For the inequality to hold we do not need to use the type
`NNReal` but can also use `Real`; and we can generalize `c` as well:
-/
lemma firstExampleNeri_general (μ : ℕ → Real) (c : NNReal)
  (h : ∀ n, μ (n + 1) ≤ c * μ n) (n : ℕ):
  μ n ≤ c^n * μ 0 := by
  induction n with
  |zero => simp only [pow_zero, one_mul, le_refl]
  |succ n hn =>
    calc
    _ ≤ c * μ n := h n
    _ ≤ _ := by
      ring_nf;
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hn c.2

/- Using rationals and nonnegative rationals works with the same proof: -/
example (μ : ℕ → Rat) (c : NNRat)
  (h : ∀ n, μ (n + 1) ≤ c * μ n) (n : ℕ):
  μ n ≤ c^n * μ 0 := by
  induction n with
  |zero => simp only [pow_zero, one_mul, le_refl]
  |succ n hn =>
    calc
    _ ≤ c * μ n := h n
    _ ≤ _ := by
      ring_nf;
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hn c.2
