import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!

#  Degrees of and lowness for isometric isomorphism

[Franklin and McNicholl](http://logicandanalysis.org/index.php/jla/article/view/6)

define a metric on a graph by:
d_G(v₀,v₁) =
0 if v₀ = v₁
1 if (v₀,v₁) ∈ E;
2 otherwise

They say this is "clearly" a metric. We prove this formally and
generalize it, by replacing 1 and 2 by real numbers
0 < a ≤ 2b, b ≤ 2a (the fact that 0 < b follows but does not need to be mentioned).

-/

open Classical
noncomputable instance franklinMcNichollMetric {U : Type}  (G : SimpleGraph U) (a b : ℝ)
(h₀ : 0 < a) (h₁ : a ≤ b + b) (h₂ : b ≤ a + a)
: MetricSpace U := {
  dist := λ x y ↦ ite (x=y) 0 (ite (G.Adj x y) a b)
  dist_self := λ x ↦ by simp only [reduceIte]
  dist_comm := λ x y ↦ by
    unfold dist
    simp
    by_cases H : x = y
    . rw [if_pos H, if_pos H.symm]
    . rw [if_neg H]
      have hne: ¬ y = x := fun a ↦ H (id (Eq.symm a))
      by_cases H' : G.Adj x y
      . rw [if_pos H', if_neg hne]
        have : G.Adj y x := SimpleGraph.adj_symm G H'
        rw [if_pos this]
      . rw [if_neg H', if_neg hne]
        have : ¬ G.Adj y x := fun a ↦ H' (SimpleGraph.adj_symm G a)
        rw [if_neg this]
  dist_triangle := λ x y z ↦ by -- aesop <;> linarith or:
      simp_all only
      split
      next h =>
        subst h
        split
        next h =>
          subst h
          simp_all only [↓reduceIte, add_zero, le_refl]
        next h =>
          split
          next h_1 =>
            split
            next h_2 =>
              subst h_2
              simp_all only [not_true_eq_false]
            next h_2 =>
              split
              next h_3 =>
                simp_all only [nonneg_add_self_iff]
                linarith
              next h_3 => linarith
          next h_1 =>
            split
            next h_2 =>
              subst h_2
              simp_all only [not_true_eq_false]
            next h_2 =>
              split
              next h_3 => linarith
              next h_3 =>
                simp_all only [nonneg_add_self_iff]
                linarith
      next h =>
        split
        next h_1 =>
          split
          next h_2 =>
            subst h_2
            simp_all only [↓reduceIte, zero_add, le_refl]
          next h_2 =>
            split
            next h_3 =>
              simp_all only [le_add_iff_nonneg_right]
              split
              next h_4 =>
                subst h_4
                simp_all only [not_false_eq_true, le_refl]
              next h_4 =>
                split
                next h_5 => linarith
                next h_5 => linarith
            next h_3 =>
              split
              next h_4 =>
                subst h_4
                simp_all only [not_false_eq_true, not_true_eq_false]
              next h_4 =>
                split
                next h_5 =>
                  simp_all only [le_add_iff_nonneg_left]
                  linarith
                next h_5 => simp_all only
        next h_1 =>
          split
          next h_2 =>
            subst h_2
            simp_all only [↓reduceIte, zero_add, le_refl]
          next h_2 =>
            split
            next h_3 =>
              split
              next h_4 =>
                subst h_4
                simp_all only [not_false_eq_true]
              next h_4 =>
                split
                next h_5 => simp_all only
                next h_5 =>
                  simp_all only [le_add_iff_nonneg_left]
                  linarith
            next h_3 =>
              simp_all only [le_add_iff_nonneg_right]
              split
              next h_4 =>
                subst h_4
                simp_all only [not_false_eq_true, le_refl]
              next h_4 =>
                split
                next h_5 => linarith
                next h_5 => linarith
  edist_dist := (λ x y ↦ by exact (ENNReal.ofReal_eq_coe_nnreal _).symm)
  eq_of_dist_eq_zero := by
    intro x y h
    simp at h
    contrapose h
    push_neg
    use h
    by_cases H : G.Adj x y
    rw [if_pos H]
    linarith
    rw [if_neg H]
    linarith
}
