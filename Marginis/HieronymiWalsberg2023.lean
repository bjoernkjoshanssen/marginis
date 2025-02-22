import Mathlib.Data.Real.Archimedean
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.MetricSpace.Basic

/-!

# Fractals and the monadic second order theory of one successor

[PHILIPP HIERONYMI and ERIK WALSBERG](http://logicandanalysis.org/index.php/jla/article/view/448)

Oscillation

Let f : (X, dX) → (Y, dY ) be
a function between metric spaces. The oscillation of f at x ∈ X is the supremum of all
δ ≥ 0 such that for every ε > 0 there are y,z ∈ X such that dX(x, y) < ε, dX(x,z) < ε
and dY (f(y), f(z)) > δ .
. Recall that f is continuous at x if and only if the oscillation of
f at x is zero.
-/

-- We need to use `ENNReal` here since the oscillation may be ∞.
noncomputable def oscillation {X Y : Type} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (x : X) : ENNReal :=
  sSup { δ : ENNReal | ∀ ε > 0, ∃ y z, edist x y < ε ∧ edist x z < ε ∧ edist (f y) (f z) > δ}

/-- The oscillation of a constant `c` is 0 at any `x`. -/
theorem oscillation_const {c x : ℝ} : oscillation (fun _ : ℝ => c) x = 0 := by
  unfold oscillation
  simp
  suffices sSup ∅ = (0 : ENNReal) by
    rw [← this]
    congr
    ext
    simp
    use 1
    simp
  have := @sSup_empty ENNReal _
  rw [this]
  simp

/-- The oscillation of the identity is 0 at any `x`. -/
theorem oscillation_id : oscillation (fun x : ℝ => x) x = 0 := by
  unfold oscillation
  simp
  have h₀ : {δ : ENNReal | ∀ (ε : ENNReal), 0 < ε → ∃ y, edist x y < ε ∧ ∃ x_1, edist x x_1 < ε ∧ δ < edist y x_1} ⊆ {0} := by
    intro δ
    simp
    by_cases H : δ = ⊤
    · subst H
      intro h
      have := h 1 (by simp)
      obtain ⟨y,hy⟩ := this
      obtain ⟨z,hz⟩ := hy.2
      simp at hz
    intro h
    by_contra H₀
    have := h (δ / 2) (by
      simp
      tauto
    )
    obtain ⟨y,hy⟩ := this
    obtain ⟨z,hz⟩ := hy.2
    have : δ < δ := calc
      _ < edist y z := by tauto
      _ ≤ edist y x + edist x z := by exact edist_triangle y x z
      _ < δ / 2 + edist x z := by
        rw [edist_comm]
        refine (ENNReal.add_lt_add_iff_right ?_).mpr ?_
        exact edist_ne_top x z
        tauto
      _ < δ / 2 + δ / 2 := by
        rw [edist_comm]
        refine (ENNReal.add_lt_add_iff_left ?_).mpr ?_
        have : δ < ⊤ := by exact Ne.lt_top' fun a ↦ H (id (Eq.symm a))
        have : δ / 2 < ⊤ := by
          refine ENNReal.div_lt_top H ?h2
          simp
        exact LT.lt.ne_top this
        rw [edist_comm]
        tauto
      _ = δ := by simp

    simp at this
  have : sSup {(0 : ENNReal)} = 0 := by exact sSup_singleton
  by_cases G : 0 ∈ {δ | ∀ (ε : ENNReal), 0 < ε → ∃ y, edist x y < ε ∧ ∃ x_1, edist x x_1 < ε ∧ δ < edist y x_1}
  · have : {δ | ∀ (ε : ENNReal), 0 < ε → ∃ y, edist x y < ε ∧ ∃ x_1, edist x x_1 < ε ∧ δ < edist y x_1} = {0}:= by
      apply subset_antisymm
      tauto
      intro z hz
      simp at hz
      subst hz
      tauto
    rw [this]
    simp
  · have : {δ | ∀ (ε : ENNReal), 0 < ε → ∃ y, edist x y < ε ∧ ∃ x_1, edist x x_1 < ε ∧ δ < edist y x_1} = ∅ := by
      apply subset_antisymm
      · intro δ hδ
        have  := h₀ hδ
        simp at this
        subst this
        tauto
      · simp
    rw [this]
    simp
