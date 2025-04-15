import Mathlib.Data.Real.Archimedean
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Oscillation

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
/--  `oscillation` was also added to Mathlib in 2024. We should prove that they coincide.
The results below can be proved for `oscillation` by observing that both functions are continuous.
-/
noncomputable def oscillation' {X Y : Type} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (x : X) : ENNReal :=
  sSup { δ : ENNReal | ∀ ε > 0, ∃ y z, edist x y < ε ∧ edist x z < ε ∧ edist (f y) (f z) > δ}

theorem toNNReal_le_ENNReal
  (b : ENNReal)
  (ε : NNReal)
  (this : b ≤ ↑ε) : b.toNNReal ≤ ε := by
    by_cases H : b = ⊤
    · aesop
    · have := @ENNReal.toNNReal_le_toNNReal b (ENNReal.ofNNReal ε) H (by aesop)
      simp at this
      tauto

theorem coincide_osc {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (x : X) : oscillation' f x = oscillation f x := by

  unfold oscillation oscillation'
  simp
  apply le_antisymm
  · refine le_iInf₂ ?_
    intro S hS
    simp only [sSup_le_iff, Set.mem_setOf_eq] at hS ⊢
    intro b h ε hε
    use b.toNNReal
    simp at hε
    have ⟨y,hy⟩ := h 1 (by simp)
    have ⟨z,hz⟩ := hy.2
    have : edist (f y) (f z) ≠ ⊤ := by exact edist_ne_top (f y) (f z)
    have : edist (f y) (f z) < ⊤ := by exact edist_lt_top (f y) (f z)
    have : b < ⊤ := by apply lt_trans hz.2 this
    have : b ≠ ⊤ := by exact LT.lt.ne_top this
    constructor
    · refine (WithTop.untop_eq_iff this).mp ?h.intro.intro.left.a
      unfold WithTop.untop
      simp
      aesop
    · suffices b ≤ ε by
        apply toNNReal_le_ENNReal _ _ this
      rw [← hε]
      -- use hS to get a certain δ
      -- rw [nhds] at hS
      -- have := @mem_nhds_iff X x (f⁻¹' S) _
      rw [mem_nhds_iff] at hS
      obtain ⟨t,ht⟩ := hS
      sorry
  ·
    sorry

/-- The oscillation' of a constant `c` is 0 at any `x`. -/
theorem oscillation'_const {c x : ℝ} : oscillation' (fun _ : ℝ => c) x = 0 := by
  unfold oscillation'
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

/-- The oscillation' of the identity is 0 at any `x`. -/
theorem oscillation'_id : oscillation' (fun x : ℝ => x) x = 0 := by
  unfold oscillation'
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
