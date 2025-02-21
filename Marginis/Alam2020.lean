import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!

# Limiting probability measures

[Irfan Alam](http://logicandanalysis.org/index.php/jla/article/view/1)

concerns integrals. Here we merely compute some.

-/

lemma int000 : ∫ (_:ℝ) in Set.Icc 0 0, (0:ℝ) = 0 := by
  simp only [Set.Icc_self, MeasureTheory.Measure.restrict_singleton,
    MeasureTheory.measure_singleton, zero_smul, MeasureTheory.integral_zero]

lemma int01xminus1 :
  (∫ (x:ℝ) in (0)..(2), (x:ℝ)) - 1 = 1 := by
  have Q := @integral_id 0 2
  ring_nf at Q
  rw [Q]
  ring_nf

lemma int02pisin :
  (∫ (x:ℝ) in (0)..(2*Real.pi), (Real.sin x)) = 0 := by
  let Q := @integral_sin 0 (2 * Real.pi)
  rw [Q]
  simp only [Real.cos_zero, Real.cos_two_pi, sub_self]

lemma int02picos :
  (∫ (x:ℝ) in (0)..(2*Real.pi), (Real.cos x)) = 0 := by
  let Q := @integral_cos 0 (2 * Real.pi)
  rw [Q]
  simp only [Real.sin_two_pi, Real.sin_zero, sub_self]

lemma int01cosSqAddSinSq :
  (∫ (x:ℝ) in (0)..(1), ((Real.cos x)^2 + (Real.sin x)^2)) = 1 := by
    simp only [Real.cos_sq_add_sin_sq]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

lemma int011 : (∫ (_:ℝ) in (0:ℝ)..(1:ℝ), (1:ℝ)) = 1 := by
  let Q := @integral_one 0 1
  rw [Q]
  simp only [sub_zero]

example (c : ℝ) : (∫ (x:ℝ) in (0:ℝ)..(1:ℝ), 1 * (c:ℝ)) = c := by
  let Q := @intervalIntegral.integral_mul_const 0 1
    MeasureTheory.volume ℝ _ c (λ _ ↦ 1)
  rw [Q,integral_one,sub_zero, one_mul]

example (c : ℝ) : (∫ (x:ℝ) in (0:ℝ)..(1:ℝ), x * (c:ℝ)) = c/2 := by
  let Q := @intervalIntegral.integral_mul_const 0 1
    MeasureTheory.volume ℝ _ c id
  show ∫ (x : ℝ) in (0:ℝ)..1, (id x) * c = c / 2
  rw [Q]
  show (∫ (x : ℝ) in (0:ℝ)..1, x) * c = c / 2
  rw [integral_id]
  simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_div]
  ring

example (f g : ℝ → ℝ) (h : ∀ x ∈ Set.Icc 0 1, f x = g x) :
  ∫ (x : ℝ) in (0)..1, f x = ∫ (x : ℝ) in (0)..1, g x := by
    refine intervalIntegral.integral_congr ?h
    simp only [zero_le_one, Set.uIcc_of_le]
    tauto
