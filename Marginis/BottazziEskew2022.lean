import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
/-!

# Integration with filters
[Emanuele Bottazzi and Monroe Eskew](http://logicandanalysis.org/index.php/jla/article/view/403)

The paper concerns measures over [0,∞].

In Lean this interval is known as the type `ENNReal`, the extended nonnegative reals.
The number `∞` is represented as `⊤`.

Here we explore the arithmetic of this type.

-/

example : (5:ENNReal) / 0 = ⊤ := by
  apply ENNReal.div_zero
  exact Ne.symm (OfNat.zero_ne_ofNat 5)

example (x : NNReal) : x / 0 = 0 := by
  exact div_zero _

example : (0:NNReal) / 0 = 0 := by
  exact zero_div 0

example : (0:ENNReal) / 0 = 0 := by
  exact ENNReal.zero_div

example : (⊤:ENNReal) / ⊤ = 0 := by
  exact ENNReal.div_top

example : (5:ENNReal) * ⊤ = ⊤ := by
  refine ENNReal.mul_top ?h
  exact Ne.symm (OfNat.zero_ne_ofNat 5)

example : (⊤ : ENNReal) / 0 = ⊤ := by
  refine ENNReal.top_div_of_lt_top ?h
  exact ENNReal.zero_lt_top

example : (0:ENNReal) * ⊤ = 0 := by
  exact zero_mul ⊤

example : (⊤:ENNReal) ^ 2 = ⊤ := by
  exact rfl

-- example (a : ENNReal) (b : NNReal) : a ^ b = a ^ b := rfl
example (a : Real) (b : Real) : a ^ b = a ^ b := rfl

example : Real.sqrt (-1) = (-1: Real) ^ ((1:Real)/2) := by
  exact Real.sqrt_eq_rpow (-1)

lemma iReal : (-1: Real) ^ ((1:Real)/2) = 0 := by
  rw [← Real.sqrt_eq_rpow]
  ring_nf
  refine Real.sqrt_eq_zero_of_nonpos ?h
  simp

example (a : NNReal) (b : Real) : a ^ b = a ^ b := rfl
example (a : ENNReal) (b : Real) : a ^ b = a ^ b := rfl

-- example : (0:ENNReal) ^ ⊤ = ⊤ := by -- not defined
--   exact rfl
