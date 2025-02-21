import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Geometric spaces with no points

[LUBARSKY](http://logicandanalysis.org/index.php/jla/article/view/64)


The paper discusses the fact that "there is no continuous square root function on any
neighborhood of 0 in the complex numbers."

Less justifiably, the Pythagoreans were hesitant to accept √2.
Here we show how √2 arises as the length of a diagonal in Euclidean geometry.

-/

def x : EuclideanSpace ℝ (Fin 2) := ![0, 0]
def y : EuclideanSpace ℝ (Fin 2) := ![1, 1]

example :  dist x y = √2 := by
  let Q := @EuclideanSpace.dist_eq ℝ _ (Fin 2) _ x y
  rw [Q]
  refine (Real.sqrt_inj ?hx ?hy).mpr ?_
  simp
  have h₀: 0 ≤ dist (x 0) (y 0) ^ 2 := sq_nonneg (dist (x 0) (y 0))
  exact Left.add_nonneg h₀ h₀
  . simp
  simp
  have g₀: dist (x 0) (y 0) = 1 := by unfold x y;simp
  have g₁: dist (x 1) (y 1) = 1 := by unfold x y;simp
  rw [g₀,g₁]
  simp
  ring
