import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Hausdorff

/-

A Constructive Examination of Rectifiability
DOUGLAS S. BRIDGES
MATTHEW HENDTLASS
ERIK PALMGREN

The first displayed equation on page 2 suggests that

sqrt ((x-y)^2 + (κ (x-y))^2) ≤ (1 + κ) * |x-y|

We verify that formally and show (see `h₀` below) that a sharper (easy) bound exists.
We need κ ≥ 0 but we do not need κ > 0. In fact, Wikipedia only requires κ ≥ 0 at https://en.wikipedia.org/wiki/Lipschitz_continuity

-/

example (x y : ℝ) (κ : ℝ) (h : 0 ≤ κ) : (x-y)^2 + (κ * (x-y))^2 ≤ (1 + κ)^2 * (x-y)^2 := by
  have h₀: (1 + κ^2) ≤ (1+κ)^2 := by linarith
  have h₁: 0 ≤ (x-y)^2 := sq_nonneg (x - y)
  have h₂: (κ * (x-y))^2 = κ^2 * (x-y)^2 := by linarith
  have h₃: (x - y) ^ 2 + κ ^ 2 * (x - y) ^ 2 = (1 + κ^2) * (x-y)^2 := by linarith
  rw [h₂,h₃]
  exact mul_le_mul_of_nonneg_right h₀ h₁
