import Mathlib.MeasureTheory.Measure.Hausdorff

/-

The paper

Quantifier elimination in the theory of
Lp(Lq)-Banach lattices
C WARD HENSON
YVES RAYNAUD

(JLA 2011)

concerns q.e. (for positive sentences) but does not give a definition of it.
Here we show how to eliminate a quantifier for a positive sentence
when calculating the range of a
simple Möbius transformation.

-/

lemma mul_of_div {a b c : ℝ} (h : a = b / c) (h₀ : c ≠ 0) : a * c = b := by
  let Q := (@mul_inv_eq_iff_eq_mul₀ ℝ _ b c a h₀).mp (by
    ring_nf at h
    linarith
  )
  linarith

lemma minu {y : ℝ} (h : y ≠ 1) : y - 1 ≠ 0 := by
      contrapose h
      simp at *
      linarith

lemma moebius_one (a b y : ℝ) (ha : a ≠ b) : (∃ x, y = (x + a) / (x + b)) ↔ y ≠ 1 := by
  constructor
  · intro h hc
    subst hc
    obtain ⟨x,hx⟩ := h
    by_cases H : x+b=0
    . rw [H] at hx
      contrapose hx
      simp
    . have h₀: 1 * (x+b) = (x+a)/(x+b) * (x+b) :=
        by rw [hx]
      have : (x + a) / (x +b) * (x + b) = x+a := by
        exact div_mul_cancel₀ (x + a) H
      contrapose ha
      simp
      linarith
  · intro h
    exists (a-b * y)/(y-1)
    apply eq_div_of_mul_eq
    . intro hc
      contrapose ha
      simp
      have : (a - b * y) = -b * (y-1) := by
        symm; exact mul_of_div (by linarith) (minu h)
      linarith
    . suffices (y-1) * ((a - b * y) / (y - 1)) + y*b = a by
        linarith
      rw [mul_div,mul_comm,mul_div_assoc]
      have h₀: (y-1)/(y-1) = 1 := (div_eq_one_iff_eq (minu h)).mpr rfl
      rw [h₀]
      linarith

example (y : ℝ) : (∃ x, y = (x + 2) / (x - 2)) ↔ y ≠ 1 := by
  apply moebius_one
  linarith
