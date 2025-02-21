import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

/-!

# K–theory of co-existentially closed continua

[CHRISTOPHER J. EAGLE and JOSHUA LAU](http://logicandanalysis.org/index.php/jla/article/view/515)

discusses algebraically closed fields.

We prove that there is a complex number z with z^2 + 2 = 0.
-/

theorem algClosExa₁ : ∃ z : ℂ, z^2 + 1 = 0 := by
  use Complex.I
  simp

theorem algClosExa₂ : ∃ z : ℂ, z^2 + 2 = 0 := by
  use (Real.sqrt 2) * Complex.I
  rw [mul_pow]
  simp
  have : (Complex.ofReal' (Real.sqrt 2))^2 = 2 := by
    rw [sq]
    norm_cast
    simp
  rw [this]
  simp
