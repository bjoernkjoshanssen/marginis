import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.ExponentialBounds

/-!

# On Preparation Theorems for R_an,exp –definable Functions
by ANDRE OPRIS

We define Example 0.1 and show that f 0 0 = 0.
A "LaTeX proof" of this would be:
since 2 < e, ln 2 < 1, so ln (ln 2) < 0
max (ln (ln 2)) 1 = 1,
and arctan (ln 1) = arctan 0 = 0.
-/

noncomputable def f (t x : ℝ) : ℝ :=
  Real.arctan <|Real.log <|max (Real.log <| t^4 + Real.log (x^2 + 2)) 1

example : f 0 0 = 0 := by
  unfold f
  simp
  right
  left
  refine (Real.log_le_iff_le_exp ?h.h.hx).mpr ?h.h.a
  refine (Real.log_pos_iff ?h.h.hx.hx).mpr ?h.h.hx.a
  exact zero_lt_two
  exact one_lt_two
  apply le_trans
  show Real.log 2 ≤ 1
  refine (Real.log_le_iff_le_exp ?h.h.a.a.hx).mpr ?h.h.a.a.a
  exact zero_lt_two
  have := Real.exp_one_gt_d9
  simp at this
  norm_cast
  norm_num
  have h₀:= @Real.exp_bound 1 (by simp) 3 (by simp)
  have g : ∑ m ∈ Finset.range 3, 1 ^ m / (m.factorial : ℝ)
    = 1^0 / ((Nat.factorial 0) : ℝ)
    + 1^1 / ((Nat.factorial 1) : ℝ)
    + 1^2 / ((Nat.factorial 2) : ℝ) := by
    rw [Finset.range_succ]
    simp
    suffices ∑ x ∈ Finset.range 2, ((Nat.factorial x) : ℝ)⁻¹ = 1 + 1 by
      linarith
    rw [Finset.range_succ]
    simp
  have h₁:  ∑ m ∈ Finset.range 3, 1 ^ m / (m.factorial : ℝ) = 5/2 := by
    rw [g]
    simp
    ring
  rw [h₁] at h₀
  simp at h₀
  have : Nat.factorial 3 = 6 := rfl
  rw [this] at h₀
  simp at h₀
  have h₃ : (4:ℝ) / (6 * 3) = 2 / 9 := by ring
  rw [h₃] at h₀
  have := @abs_le ℝ _ (Real.exp 1 - 5/2) (2/9)
  have := (this.mp h₀).1
  linarith
  apply Real.one_le_exp
  exact zero_le_one' ℝ
