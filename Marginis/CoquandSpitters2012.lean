import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Init.Set

 /-

In the paper
A constructive proof of Simpson’s Rule
THIERRY COQUAND BAS SPITTERS

uniform continuity is discussed.

We define it in a concrete setting here, and prove formally that:

 - y = 2x is uniformly continuous on ℝ.
 - y = x² is not uniformly continuous on ℝ.
 - z = y² - x² is not uniformly continuous on ℝ².
 - y = x² is uniformly continuous on [0,1].

-/

open Classical

def is_limit (a L : ℝ) (f : ℝ → ℝ) : Prop := ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |(f x) - L| < ε

noncomputable def is_limit_bool (a : ℝ) (f : ℝ → ℝ) (L:ℝ) : Bool := ite (is_limit a L f) true false



def is_uniformly_continuous (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x y : ℝ, |x - y| < δ → |(f x) - (f y)| < ε

def is_uniformly_continuous₂ (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
  ∃ δ : ℝ, δ > 0 ∧ ∀ p q : ℝ × ℝ,
  (p.1 - q.1)^2 + (p.2 - q.2)^2 < δ^2 → |(f p) - (f q)| < ε


lemma extraabs (a : ℝ) (h : 0 < a) : 1 ≤ |1 + a| := by
  refine (one_le_sq_iff_one_le_abs (1 + a)).mp ?_
  ring_nf
  have h0 : 0 ≤ a := le_of_lt h
  have h1 : - a^2 ≤ 0 := neg_nonpos.mpr (sq_nonneg a)
  have h2 : 0 ≤ a * 2 := mul_nonneg h0 zero_le_two
  have h3 : 0 ≤ a * 2 + a ^ 2 :=
    neg_le_iff_add_nonneg.mp (Preorder.le_trans (-a ^ 2) 0 (a * 2) h1 h2)
  have h4 : 1 ≤ 1 + a * 2 + a ^ 2 := by
    refine neg_le_sub_iff_le_add.mp ?_
    ring_nf
    exact neg_le_iff_add_nonneg.mpr h3
  exact h4


example : is_uniformly_continuous (λ x ↦ 2 * x) := by
  unfold is_uniformly_continuous
  intro ε hε
  use ε / 2
  constructor
  . exact half_pos hε
  . intro x y hxy
    simp
    have r1 : 2 * x - 2 * y = 2 * (x - y) := by ring_nf
    rw [r1, abs_mul]
    simp
    have h02 : (0 : ℝ) < 2 := zero_lt_two
    have r2 : (ε / 2) * 2 = ε := by simp
    have h : |x - y| * 2 < (ε / 2) * 2 := (mul_lt_mul_right h02).mpr hxy
    rw [r2, mul_comm] at h
    exact h


lemma Hδ (δ : ℝ) (hδ : 0 < δ) : 1 ≤ |δ * δ⁻¹ + δ ^ 2 * (1 / 4)| := by
  rw [CommGroupWithZero.mul_inv_cancel δ (Ne.symm (ne_of_lt hδ))]
  have h0 : 0 < δ ^ 2 * (1 / 4) := by
    simp
    exact sq_pos_of_pos hδ
  exact extraabs (δ ^ 2 * (1 / 4)) h0

lemma transition (x y : ℝ) (ha : 0 ≤ x) (hb : 0 < y) : x < y ↔ x^2 < y^2 := Iff.symm (pow_lt_pow_iff_left ha (le_of_lt hb) (Ne.symm (Nat.zero_ne_add_one 1)))



example : ¬ is_uniformly_continuous (λ x ↦ x^2) := by
  unfold is_uniformly_continuous
  contrapose
  push_neg
  intro
  use 1
  constructor
  . exact Real.zero_lt_one
  . intro δ hδ
    use 1/δ
    use (1/δ + δ/2)
    constructor
    . ring_nf
      have h : ((-1/2) : ℝ) < 0 := div_neg_of_neg_of_pos neg_one_lt_zero zero_lt_two
      rw [abs_mul, abs_of_pos hδ, abs_of_neg h]
      ring_nf
      exact mul_lt_of_lt_one_right hδ one_half_lt_one
    . ring_nf
      have r1 : -(δ * δ⁻¹) + δ ^ 2 * (-1 / 4) = -(δ * δ⁻¹ + δ ^ 2 * (1 / 4)) := by ring_nf
      rw [r1, abs_neg (δ * δ⁻¹ + δ ^ 2 * (1 / 4))]
      exact Hδ δ hδ


example : ¬ is_uniformly_continuous₂ (λ x ↦ ((x.2^2 - x.1^2):ℝ)) := by
  unfold is_uniformly_continuous₂
  contrapose
  intro
  push_neg
  use 1
  constructor
  . exact Real.zero_lt_one
  . intro δ hδ
    use (1/δ, 0)
    use (1/δ + δ/2, 0)
    constructor
    . simp
      rw [Eq.symm (div_pow δ 2 2)]
      refine (transition (δ / 2) δ ?h.left.ha hδ).mp ?h.left.a
      exact div_nonneg (le_of_lt hδ) zero_le_two
      exact div_two_lt_of_pos hδ
    . ring_nf
      exact Hδ δ hδ


def is_uniformly_continuous_on (S : Set ℝ) (f : ↑S → ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
  ∀ x y : ↑S, |x.1 - y.1| < δ → |(f x) - (f y)| < ε

def is_uniformly_continuous_on' (R S : Set ℝ) (h : R ⊆ S) (f : ↑S → ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
  ∀ x y : ↑R, |x.1 - y.1| < δ → |(f ⟨x.1, h x.2⟩) - (f ⟨y.1, h y.2⟩)| < ε

example : is_uniformly_continuous_on' (Set.Icc 0 1) univ h (λ x ↦ x^2) := by
  unfold is_uniformly_continuous_on'
  intro ε hε
  use ε / 2
  have hε2 := half_pos hε
  constructor
  . exact hε2
  . intro x y hxy
    simp
    have r1 : |x.1 ^ 2 - y.1 ^ 2| = |(x.1 - y.1) * (x.1 + y.1)| := by ring_nf
    rw [r1, abs_mul (x.1 - y.1) (x.1 + y.1)]
    cases eq_or_ne (x.1 + y.1) 0 with
    | inl zero =>
      rw [zero]
      simp
      exact hε
    | inr not_zero =>
      have hx : |x.1| ≤ 1 := abs_le.mpr ⟨Preorder.le_trans (-1) 0 x.1 (le_of_lt neg_one_lt_zero) x.2.1, x.2.2⟩
      have hy : |y.1| ≤ 1 := abs_le.mpr ⟨Preorder.le_trans (-1) 0 y.1 (le_of_lt neg_one_lt_zero) y.2.1, y.2.2⟩
      calc
      _ < ε / 2 * |(x.1 + y.1)|         := mul_lt_mul_of_pos_right hxy ((IsAbsoluteValue.abv_pos abs).mpr not_zero)
      _ ≤ ε / 2 * (|x.1| + |y.1|)       := (mul_le_mul_iff_of_pos_left hε2).mpr (abs_add x.1 y.1)
      _ = ε / 2 * |x.1| + ε / 2 * |y.1| := by ring_nf
      _ ≤ ε / 2 * 1 + ε / 2 * |y.1|     := add_le_add_right ((mul_le_mul_iff_of_pos_left hε2).mpr hx) _
      _ = ε / 2 * |y.1| + ε / 2 * 1     := by ring_nf
      _ ≤ ε / 2 * 1 + ε / 2 * 1         := add_le_add_right ((mul_le_mul_iff_of_pos_left hε2).mpr hy) _
      _ = ε := by simp
