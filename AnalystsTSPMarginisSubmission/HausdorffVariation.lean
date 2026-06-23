/-
Copyright (c) 2026 Austin Anderson and Tony Ou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson, Tony Ou
Assisted by Gemini (AI assistant)
-/

import Mathlib
import WeierstrassLimitR2
open scoped MeasureTheory
open Set Topology

/--
The goal of this file is to prove that for any continuous parameterization `φ`,
its 1D Hausdorff measure is bounded strictly by its sequential trajectory variation.
Instead of relying on unavailable arc-length reparameterization calculus, we use
Topological Sequence Covers using compactness and `ediam`.

For any continuous curve segment `φ([A, B])`, the geometric diameter of that segment
is physically achieved by two explicit sequence points `x, y ∈ [A, B]`.
-/
lemma compact_segment_diameter_achieved (φ : ℝ → ℝ × ℝ) (h_cont : Continuous φ) (A B : ℝ) (h_le : A ≤ B) :
  ∃ x y : ℝ, A ≤ x ∧ x ≤ B ∧ A ≤ y ∧ y ≤ B ∧
  Metric.ediam (φ '' Icc A B) = edist (φ x) (φ y) := by {
  -- The interval `[A, B]` is compact.
  have h_cpt : IsCompact (Icc A B) := isCompact_Icc
  -- Since `φ` is continuous, the image is compact.
  have h_img_cpt : IsCompact (φ '' Icc A B) := h_cpt.image h_cont

  -- But we also know the interval is nonempty.
  have h_nonempty : (Icc A B).Nonempty := nonempty_Icc.mpr h_le
  have h_img_nonempty : (φ '' Icc A B).Nonempty := h_nonempty.image φ

  -- A compact non-empty set achieves its diameter via the Continuous Extreme Value Theorem over S × S
  have h_prod_cpt : IsCompact ((φ '' Icc A B) ×ˢ (φ '' Icc A B)) := h_img_cpt.prod h_img_cpt
  have h_prod_nonempty : ((φ '' Icc A B) ×ˢ (φ '' Icc A B)).Nonempty := Set.Nonempty.prod h_img_nonempty h_img_nonempty
  have h_cont_edist : ContinuousOn (fun p : (ℝ × ℝ) × (ℝ × ℝ) => edist p.1 p.2) ((φ '' Icc A B) ×ˢ (φ '' Icc A B)) := continuous_edist.continuousOn

  -- The Extreme Value Theorem strictly forces a maximum to exist physically inside the compact domain!
  have h_max := IsCompact.exists_isMaxOn h_prod_cpt h_prod_nonempty h_cont_edist
  rcases h_max with ⟨⟨p1, p2⟩, hp_mem, h_is_max⟩

  -- Since p1 and p2 are in the image `φ '' Icc A B`, they map back to physical coordinates x and y in `[A, B]`
  rcases hp_mem.1 with ⟨x, hx_mem, hx_eq⟩
  rcases hp_mem.2 with ⟨y, hy_mem, hy_eq⟩

  use x, y
  rw [hx_eq, hy_eq]

  -- Now prove the maximum value equals the formal diameter definition
  have h_le : edist p1 p2 ≤ Metric.ediam (φ '' Icc A B) := Metric.edist_le_ediam_of_mem hp_mem.1 hp_mem.2
  have h_ge : Metric.ediam (φ '' Icc A B) ≤ edist p1 p2 := by
    apply Metric.ediam_le
    intro u hu v hv
    have h_prod_mem : (u, v) ∈ ((φ '' Icc A B) ×ˢ (φ '' Icc A B)) := ⟨hu, hv⟩
    exact h_is_max h_prod_mem

  exact ⟨hx_mem.1, hx_mem.2, hy_mem.1, hy_mem.2, le_antisymm h_ge h_le⟩
}

/--
Mapping extracted geometric extrema limit points `x` and `y` back into ordered sorting dynamically
forms a monotonic sequence subset perfectly bounded inside `eVariationOn` boundaries!
-/
lemma diameter_bounds_monotone_sequence (u_n u_next x y : ℝ)
  (hx : u_n ≤ x ∧ x ≤ u_next)
  (hy : u_n ≤ y ∧ y ≤ u_next) :
  u_n ≤ min x y ∧ min x y ≤ max x y ∧ max x y ≤ u_next := by {
  exact ⟨le_min hx.1 hy.1, min_le_max, max_le hx.2 hy.2⟩
}

/--
Explicit sequence generating function slicing the `[0, 1]` continuum into consecutive sub-intervals
where no interval expands geometrically wider than generic metric step bounds `δ`.
-/
lemma delta_cover_sequence (δ : ℝ) (hδ : 0 < δ) :
  ∃ (u : ℕ → ℝ), u 0 = 0 ∧ (∀ i, u i ≤ u (i+1)) ∧ (∀ i, u (i+1) - u i ≤ δ) ∧ (∀ i, 0 ≤ u i) ∧ (∀ i, u i ≤ 1) ∧ ∃ N, ∀ i ≥ N, u i = 1 := by {
  -- Let `u i = min (i * δ) 1`. This naturally bounds at 1, starts at 0, and step size is max δ!
  use fun i => min (i * δ) 1

  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp
    apply min_le_min_right
    apply mul_le_mul_of_nonneg_right
    · exact Nat.cast_le.mpr (Nat.le_succ i)
    · exact le_of_lt hδ
  · intro i
    dsimp
    have h_split : ↑(i + 1) * δ = ↑i * δ + δ := by
      push_cast
      ring
    rw [h_split]
    -- We want to prove `min (A + δ) 1 - min A 1 ≤ δ`.
    -- Since `min X 1 ≤ X`, we have `min (A+δ) 1 ≤ A + δ`.
    -- If `A ≥ 1`, both mins are 1, difference is 0 ≤ δ.
    -- To avoid dense case tracking, Lean supports direct min resolution:
    rcases le_total (↑i * δ) 1 with h_le | h_ge
    · -- case A ≤ 1
      rw [min_eq_left h_le]
      -- `min (A+δ) 1 ≤ A + δ`, so `min (A+δ) 1 - A ≤ δ`
      have h_min : min (↑i * δ + δ) 1 ≤ ↑i * δ + δ := min_le_left _ _
      linarith
    · -- case A ≥ 1
      have h_ge1 : ↑i * δ + δ ≥ 1 := by linarith
      rw [min_eq_right h_ge, min_eq_right h_ge1]
      linarith
  · intro i
    exact le_min (mul_nonneg (Nat.cast_nonneg i) (le_of_lt hδ)) zero_le_one
  · intro i
    exact min_le_right _ _
  · -- Prove N = ceil (1 / δ) hits bounds!
    -- Rather than formalizing `ceil`, any sufficiently large float satisfies Archimedean properties.
    have h_arch := exists_nat_gt (1 / δ)
    rcases h_arch with ⟨N, hN⟩
    use N
    intro i hi
    dsimp
    have hi_cast : (N : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr hi
    have h_prod : 1 ≤ ↑i * δ := by
      calc 1 = (1 / δ) * δ := (div_mul_cancel₀ 1 (ne_of_gt hδ)).symm
           _ ≤ N * δ := mul_le_mul_of_nonneg_right (le_of_lt hN) (le_of_lt hδ)
           _ ≤ i * δ := mul_le_mul_of_nonneg_right hi_cast (le_of_lt hδ)
    exact min_eq_right h_prod
}

/--
Verifies that the geometric maximum diameter spanning any continuous parameter space mathematically
can never exceed the sequence supremum distance tracked sequentially by its total variation sum limits.
-/
lemma ediam_le_eVariationOn (φ : ℝ → ℝ × ℝ) (h_cont : Continuous φ)
  (A B : ℝ) (h_le : A ≤ B) :
  Metric.ediam (φ '' Icc A B) ≤ eVariationOn φ (Icc A B) := by {
  by_cases h_empty : (Icc A B).Nonempty
  · have h_diam := compact_segment_diameter_achieved φ h_cont A B h_le
    rcases h_diam with ⟨x, y, hx_ge, hx_le, hy_ge, hy_le, h_diam_eq⟩
    rw [h_diam_eq]
    have hx_mem : x ∈ Icc A B := ⟨hx_ge, hx_le⟩
    have hy_mem : y ∈ Icc A B := ⟨hy_ge, hy_le⟩
    exact eVariationOn.edist_le φ hx_mem hy_mem
  · rw [Set.not_nonempty_iff_eq_empty.mp h_empty, Set.image_empty, Metric.ediam_empty]
    exact zero_le
}

/--
Resolves continuous variation summations iteratively across parameter space topologies, 
proving that bounded sequence closures strictly collapse perfectly inside sequential monotonic metric loops.
-/
lemma eVariationOn_sequence_sum_bounded (φ : ℝ → ℝ × ℝ)
  (u : ℕ → ℝ) (hu_mono : ∀ i, u i ≤ u (i+1)) (N : ℕ) :
  (∑ i ∈ Finset.range N, eVariationOn φ (Icc (u i) (u (i+1)))) ≤ eVariationOn φ (Icc (u 0) (u N)) := by {
  have hu_monotone : Monotone u := monotone_nat_of_le_succ hu_mono
  induction' N with N ih
  · simp
  · rw [Finset.sum_range_succ]
    have h_u_le_prev : u 0 ≤ u N := hu_monotone (Nat.zero_le N)
    have h_add := eVariationOn.Icc_add_Icc (s := univ) φ h_u_le_prev (hu_mono N) (Set.mem_univ (u N))
    simp only [Set.univ_inter] at h_add
    rw [← h_add]
    exact add_le_add ih le_rfl
}

/--
Mathematically guarantees that the sequential extrema mappings defined by the delta steps
provide a complete, unbroken metric cover of the subset sequence space `[0, 1]`.
-/
lemma cover_sequence_subset (φ : ℝ → ℝ × ℝ) (u : ℕ → ℝ) (h0 : u 0 = 0)
  (hM : ∀ i, u i ≤ u (i+1)) (N : ℕ) (hN : ∀ i ≥ N, u i = 1) :
  φ '' Icc 0 1 ⊆ ⋃ (n : ℕ), φ '' Icc (u n) (u (n+1)) := by {
  rintro p ⟨x, hx, rfl⟩
  -- Extract boundary hit via the well-ordering of natural limits
  have h_ex : ∃ i, x ≤ u i := ⟨N, by rw [hN N le_rfl]; exact hx.2⟩
  let n := Nat.find h_ex
  have hn_prop : x ≤ u n := Nat.find_spec h_ex

  -- Case branch the minimum subset hit natively ensuring continuous closure
  by_cases hn_zero : n = 0
  · rw [hn_zero] at hn_prop
    rw [h0] at hn_prop
    have hx_zero : x = 0 := le_antisymm hn_prop hx.1
    rw [hx_zero]
    apply subset_iUnion _ 0
    refine ⟨0, ?_, rfl⟩
    have h1 : 0 ≤ u 1 := by rw [← h0]; exact hM 0
    exact ⟨by rw [h0], h1⟩
  · have hn_gt : 0 < n := Nat.pos_of_ne_zero hn_zero
    let m := n - 1
    have hm_succ : m + 1 = n := Nat.sub_add_cancel hn_gt
    have h_not_m : ¬ (x ≤ u m) := Nat.find_min h_ex (by omega)
    push Not at h_not_m
    apply subset_iUnion _ m
    refine ⟨x, ⟨le_of_lt h_not_m, by rw [hm_succ]; exact hn_prop⟩, rfl⟩
}

/--
Verifies that sequence boundaries built at exactly half-metric constraints
force inner segment topological bounds to satisfy open strict measure closures unconditionally.
-/
lemma uniform_segment_diameter_bounded (φ : ℝ → ℝ × ℝ) (h_cont : Continuous φ)
  (u : ℕ → ℝ) (n : ℕ) (δ r_eff : ℝ) (hδ_pos : 0 < δ)
  (hu_mono : ∀ i, u i ≤ u (i+1))
  (hu_bound : ∀ i, u (i+1) - u i ≤ δ / 2)
  (hu_mem : ∀ i, u i ∈ Icc (0:ℝ) 1)
  (h_uc : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, dist x y < δ → dist (φ x) (φ y) < r_eff) :
  Metric.ediam (φ '' Icc (u n) (u (n+1))) ≤ ENNReal.ofReal r_eff := by {

  -- The physical sequence is mathematically constrained into boundaries!
  by_cases h_empty : (Icc (u n) (u (n+1))).Nonempty
  · -- Find the exact physical bounds x, y forcing the maximal diameter distance
    have h_diam := compact_segment_diameter_achieved φ h_cont (u n) (u (n+1)) (hu_mono n)
    rcases h_diam with ⟨x, y, hx_ge, hx_le, hy_ge, hy_le, h_diam_eq⟩

    -- Using the topological limits of `[u n, u_{n+1}]`, we geometrically bound local coordinates
    have h_dist : dist x y ≤ u (n+1) - u n := by
      rw [Real.dist_eq]
      -- Since they lie inside the bounds, their absolute difference is naturally smaller than width
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

    -- Chaining this sequentially up to the sequence bounds constraints:
    have h_dist_strict : dist x y < δ := by
      calc dist x y ≤ u (n+1) - u n := h_dist
           _ ≤ δ / 2 := hu_bound n
           _ < δ := half_lt_self hδ_pos

    -- Verify coordinate domain locations natively since u n, u (n+1) ∈ [0, 1]
    have hx_mem_Icc : x ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu_mem n |>.1], by linarith [hu_mem (n+1) |>.2]⟩
    have hy_mem_Icc : y ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu_mem n |>.1], by linarith [hu_mem (n+1) |>.2]⟩

    -- Map exact distances uniformly up mapping coordinates!
    have h_uc_apply := h_uc x hx_mem_Icc y hy_mem_Icc h_dist_strict

    -- Resolve exactly by bridging real coordinates back to Extended Metric Bounds limit
    rw [h_diam_eq]
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (le_of_lt h_uc_apply)
  · -- Empty subset limits trivially evaluate 0 metric spaces
    rw [Set.not_nonempty_iff_eq_empty.mp h_empty, Set.image_empty, Metric.ediam_empty]
    exact zero_le
}

/--
By the topological consequence of continuous mappings on compact sequences,
any distance limitation `ε` corresponds necessarily to a rigorous sequential chunk constraint `δ`.
-/
lemma continuous_forces_uniform_geometric_bounds (φ : ℝ → ℝ × ℝ) (h_cont : Continuous φ) :
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, dist x y < δ → dist (φ x) (φ y) < ε := by {
  have h_cpt : IsCompact (Icc (0:ℝ) 1) := isCompact_Icc
  have h_uc := IsCompact.uniformContinuousOn_of_continuous h_cpt h_cont.continuousOn
  exact Metric.uniformContinuousOn_iff.mp h_uc
}

lemma continuous_variation_bounds_hausdorff (φ : ℝ → ℝ × ℝ) (h_cont : Continuous φ) :
  μH[1] (φ '' Icc (0:ℝ) 1) ≤ eVariationOn φ (Icc (0:ℝ) 1) := by {
  -- Under the Continuous Cover Strategy, we observe that since `Icc 0 1` is compact,
  -- and `φ` is continuous, any sub-segment `φ([u_i, u_{i+1}])` is compact.
  -- Thus its geometric diameter `ediam` is physically achieved by two parameter points `x, y ∈ [u_i, u_{i+1}]`.

  -- Because `eVariationOn` is the supremum over ALL finite monotonic sequences,
  -- adding these specific bounding points `x, y` to any sequence partition automatically
  -- proves that the geometric diameter sum is bounded by the sequence variation.

  -- Unpacking Carathéodory's Hausdorff measure definition natively from Mathlib
  rw [MeasureTheory.Measure.hausdorffMeasure_apply (d := 1)]

  -- The Hausdorff measure is the limit infimum of sequence covers over geometric width `r`.
  -- To satisfy `≤ eVariationOn`, we must prove that for ANY `r > 0`, there exists a sequence
  -- subset `t n` bounding the 1D variations generated by our earlier theorems.
  simp_rw [ENNReal.rpow_one]
  apply iSup_le
  intro r
  apply iSup_le
  intro hr_pos

  -- Instead of opening a rabbit hole tracing topological `r = ⊤` infinities directly,
  -- we can strictly define an effective metric boundary. If Carathéodory's width bound `r` is ∞,
  -- we simply use a step proxy `r_eff = 1`. Any partition bounding `1` trivially bounds `< ∞`.
  have hr_eff_pos : 0 < (if r = ⊤ then 1 else r.toReal) := by
    split_ifs with h_top
    · exact zero_lt_one
    · exact ENNReal.toReal_pos hr_pos.ne' h_top

  -- (1) Select the monotonic partition segments ensuring every internal parameter subset `[u_i, u_{i+1}]`
  -- yields an `ediam (φ '' [u_i, u_{i+1}]) ≤ r_eff` utilizing the `continuous_forces_uniform_geometric_bounds` uniform limit!
  have h_bound := continuous_forces_uniform_geometric_bounds φ h_cont (if r = ⊤ then 1 else r.toReal) hr_eff_pos
  rcases h_bound with ⟨δ, hδ_pos, h_unif⟩

  -- (2) Assign `x, y` inside each block strictly bounding the `ediam` map using `compact_segment_diameter_achieved`
  -- by pulling the sequence bounds from the `delta_cover_sequence` topological slices.
  -- Note: We inject δ/2 explicitly to geometrically lock uniform open mappings natively!
  have hδ_half : 0 < δ / 2 := half_pos hδ_pos
  have h_seq := delta_cover_sequence (δ / 2) hδ_half
  rcases h_seq with ⟨u, hu0, hu_mono, hu_bound, hu_zero, hu_one, ⟨N, hN⟩⟩

  -- Execute the instantiation of the topological bound limits inside Mathlib `hausdorffMeasure_apply`
  let t : ℕ → Set (ℝ × ℝ) := fun n => φ '' Icc (u n) (u (n+1))

  -- Unroll the complex limit infimum definitions from Carathéodory's algorithm layers cleanly
  refine le_trans (iInf_le _ t) ?_
  refine le_trans (iInf_le _ ?_) ?_
  · -- Proof Branch 1: The sequence slices strictly cover the entire continuum `φ '' [0, 1]`
    exact cover_sequence_subset φ u hu0 hu_mono N hN
  · refine le_trans (iInf_le _ ?_) ?_
    · -- Proof Branch 2: Every individual segment subset holds a diameter less than the geometric bound `r`
      intro n
      -- Derive basic parameter sequence bounds
      have hu_mem : ∀ i, u i ∈ Icc (0:ℝ) 1 := fun i => ⟨hu_zero i, hu_one i⟩
      -- Validate exact sequence parameter scaling against the generic Metric space boundaries
      have h_seg := uniform_segment_diameter_bounded φ h_cont u n δ (if r = ⊤ then 1 else r.toReal) hδ_pos hu_mono hu_bound hu_mem h_unif
      
      -- Explicitly typecast the topological limits resolution bridging finite variables to ENNReal topologies!
      have h_r_bound : ENNReal.ofReal (if r = ⊤ then 1 else r.toReal) ≤ r := by
        by_cases hr_top : r = ⊤
        · rw [hr_top]
          exact le_top
        · rw [if_neg hr_top]
          exact le_of_eq (ENNReal.ofReal_toReal hr_top)
          
      exact le_trans h_seg h_r_bound
    · -- Proof Branch 3: The infinite sum of sequence diameters limits completely inside `eVariationOn` supremum
      have h_bound_val : ∀ n, (⨆ (_ : (t n).Nonempty), Metric.ediam (t n)) ≤ eVariationOn φ (Icc (u n) (u (n+1))) := by
        intro n
        apply iSup_le
        intro _
        have hu_le : u n ≤ u (n+1) := hu_mono n
        exact ediam_le_eVariationOn φ h_cont (u n) (u (n+1)) hu_le
      
      have h_tsum_le : (∑' n, ⨆ (_ : (t n).Nonempty), Metric.ediam (t n)) ≤ ∑' n, eVariationOn φ (Icc (u n) (u (n+1))) := ENNReal.tsum_le_tsum h_bound_val
      
      -- Any limits tracing out beyond mathematical closure trivially shrink geometrically to exact points natively
      have h_zero : ∀ n ≥ N, eVariationOn φ (Icc (u n) (u (n+1))) = 0 := by
        intro n hn
        have hn1 : N ≤ n + 1 := by linarith
        rw [hN n hn, hN (n+1) hn1]
        have h_sub : (Icc (1:ℝ) 1).Subsingleton := by
          rintro _ ⟨h1, h2⟩ _ ⟨h3, h4⟩
          linarith
        exact eVariationOn.subsingleton φ h_sub
        
      -- Finite bounds map natively back cleanly!
      have h_tsum_eq : (∑' n, eVariationOn φ (Icc (u n) (u (n+1)))) = ∑ i ∈ Finset.range N, eVariationOn φ (Icc (u i) (u (i+1))) := by
        apply tsum_eq_sum
        intro n hn
        have hn_ge : n ≥ N := by rwa [Finset.mem_range, not_lt] at hn
        exact h_zero n hn_ge
        
      -- Validate and lock tracking bounds sequence strictly onto subsets
      rw [h_tsum_eq] at h_tsum_le
      have h_sum_le_var := eVariationOn_sequence_sum_bounded φ u hu_mono N
      
      -- Clean domains explicitly bridging natively back fully into [0, 1] topological limits mathematically!
      have hu0_val : u 0 = 0 := hu0
      have huN_val : u N = 1 := hN N le_rfl
      rw [hu0_val, huN_val] at h_sum_le_var
      
      exact le_trans h_tsum_le h_sum_le_var
}
