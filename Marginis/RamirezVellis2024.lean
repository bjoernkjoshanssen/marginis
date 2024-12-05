import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

/-!

# Time complexity of the Analyst’s Traveling Salesman algorithm
by
ANTHONY RAMIREZ
VYRON VELLIS

We prove for any `N` the `n = 2` version of
the statement on page 3 containing the phrase "it is clear that".
-/

theorem clear {N : ℕ} (v w : Fin N → ℝ) :
  let R₀ := 5 * max (dist v 0) (dist w 0)
  ∀ i, v i ∈ Set.Icc (- R₀) R₀ := by
  intro R₀ i
  simp
  constructor
  · suffices  - max (dist v 0) (dist w 0) ≤ v i by
      apply LE.le.trans
      show - R₀ ≤ - max (dist v 0) (dist w 0)
      unfold R₀
      have : 0 ≤ max (dist v 0) (dist w 0) := by
        apply le_max_iff.mpr
        left
        exact dist_nonneg
      refine neg_le_neg_iff.mpr ?_
      suffices 1 * max (dist v 0) (dist w 0) ≤ 5 * max (dist v 0) (dist w 0) by
        simp_all
      apply mul_le_mul
      exact Nat.one_le_ofNat
      exact Preorder.le_refl (max (dist v 0) (dist w 0))
      exact this
      exact Nat.ofNat_nonneg' 5
      exact this
    suffices - v i ≤ max (dist v 0) (dist w 0) by exact neg_le.mp this
    apply le_max_iff.mpr
    left
    apply le_trans
    show - v i ≤ |v i|
    exact neg_le_abs (v i)
    have := dist_le_pi_dist v 0 i
    simp at this
    have : dist (v i) 0 = |v i| := by exact Real.dist_0_eq_abs (v i)
    aesop
  · suffices v i ≤ max (dist v 0) (dist w 0) by
      apply le_trans
      exact this
      unfold R₀
      suffices 1 * max (dist v 0) (dist w 0) ≤ 5 * max (dist v 0) (dist w 0) by
        simp_all
      apply mul_le_mul
      exact Nat.one_le_ofNat
      exact Preorder.le_refl (max (dist v 0) (dist w 0))
      apply le_max_iff.mpr
      left
      exact dist_nonneg
      exact Nat.ofNat_nonneg' 5
    apply le_max_iff.mpr
    left
    have := dist_le_pi_dist v 0 i
    simp at this
    apply le_trans
    show v i ≤ dist (v i) ((fun _ => 0) i)

    apply le_trans
    show v i ≤ |v i|
    exact le_abs_self (v i)
    simp
    have : dist (v i) 0 = |v i - 0| := rfl
    rw [this]
    simp
    exact this
