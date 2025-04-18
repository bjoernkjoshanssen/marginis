import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!

## Topometric characterization of type spaces in continuous logic
James Hanson

-/

def S := (Set.Icc (0:ℝ) 1) × ℕ

instance : TopologicalSpace S := instTopologicalSpaceProd -- ChatGPT

/-- We prove that without the point at infinity, the metric in the proof of Example 1.2
really is a metric. -/
instance : MetricSpace S := {
  dist := fun (x,m) (y,n) => ite (m = n) |x - y| 1
  dist_self := fun x => by simp;aesop
  dist_comm := fun x y => by
    simp
    split
    rename_i x y_1 n
    obtain ⟨val, property⟩ := y_1
    simp_all only
    simp_all only [Set.mem_Icc]
    split
    rename_i x_1 y n_1
    obtain ⟨val_1, property⟩ := y
    simp_all only
    simp_all only [Set.mem_Icc]
    split
    next h =>
      subst h
      simp_all only [↓reduceIte]
      exact abs_sub_comm val val_1
    next h =>
      split
      next h_1 =>
        subst h_1
        simp_all only [not_true_eq_false]
      next h_1 => simp_all only
  dist_triangle := fun x y z => by
    simp
    split
    rename_i x y_1 n
    obtain ⟨val, property⟩ := y_1
    simp_all only
    simp_all only [Set.mem_Icc]
    obtain ⟨left, right⟩ := property
    split
    rename_i x_1 y_1 n_1
    obtain ⟨val_1, property⟩ := y_1
    simp_all only
    simp_all only [Set.mem_Icc]
    obtain ⟨left_1, right_1⟩ := property
    split
    next h =>
      subst h
      split
      rename_i x_2 y n_1
      obtain ⟨val_2, property⟩ := y
      simp_all only
      simp_all only [Set.mem_Icc]
      split
      next h =>
        subst h
        simp_all only [↓reduceIte]
        exact abs_sub_le val val_2 val_1
      next h =>
        split
        next h_1 =>
          subst h_1
          simp_all only [not_true_eq_false]
        next h_1 =>
          refine abs_sub_le_iff.mpr ?_
          constructor
          linarith
          linarith
    next h =>
      split
      rename_i x_2 y n_2
      obtain ⟨val_2, property⟩ := y
      simp_all only
      simp_all only [Set.mem_Icc]
      split
      next h_1 =>
        subst h_1
        simp_all only [↓reduceIte, le_add_iff_nonneg_left, abs_nonneg]
      next h_1 =>
        simp_all only [le_add_iff_nonneg_right]
        split
        next h_2 =>
          subst h_2
          simp_all only [not_false_eq_true, abs_nonneg]
        next h_2 => simp_all only [zero_le_one]
  eq_of_dist_eq_zero := by
    simp
    intro x y a
    split at a
    rename_i x y_1 n
    split at a
    rename_i x_1 y n_1
    split at a
    next h =>
      subst h
      simp_all only [abs_eq_zero]
      obtain ⟨val, property⟩ := y_1
      obtain ⟨val_1, property_1⟩ := y
      simp_all only
      congr
      linarith
    next h => simp_all only [one_ne_zero]
}
