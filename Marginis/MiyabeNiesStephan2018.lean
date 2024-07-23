import Mathlib.MeasureTheory.Measure.Hausdorff
/-

Miyabe, Nies, Stephan, `Randomness and Solovay degrees`, JLA, 2018, page 3 says:

`We sometimes identify a real α with its binary expansion X ∈ 2^ω`
`and the corresponding set X = {n ∈ ℕ : X (n) = 1 }`

Here we prove the well known fact that this representation is not unique.

We also show that consequently, if we use `Mathlib`'s current definition of
the pullback measure as of June 23, 2024 as a basis for a measure on Cantor space,
the Cantor space gets measure 0.
 -/

lemma geom_value : ∑' (n : ℕ), ((1:ℝ) / 2 ^ n.succ)  = 1 := by
        let E := tsum_geometric_two' 1;simp at E
        nth_rewrite 2 [← E];apply tsum_congr;intro b
        norm_num;ring_nf

lemma geom_summable: Summable (λ n : ℕ ↦ (1:ℝ) / 2^n.succ) := by
      have : (fun i ↦ (1:ℝ) / 2^(i+1)) = (fun n ↦ (1/2)^(n) * (1/2)) := by
            apply funext;intro x;ring_nf
      let T := @summable_mul_right_iff ℕ ℝ _ _ _ (λ x ↦ (1 / 2)^x) (1/2) (by simp)
      rw [this, T]
      exact @NormedRing.summable_geometric_of_norm_lt_one
                ℝ _ _ (1/2) (by simp; exact two_inv_lt_one)

noncomputable def real_of_cantor :=
  λ (x : ℕ → Bool) ↦ tsum (λ n : ℕ ↦ ite (x n = true) ((1:ℝ) / (2 ^ n.succ)) 0)

noncomputable def CantorLebesgueMeasure : MeasureTheory.Measure (ℕ → Bool) :=
MeasureTheory.Measure.comap real_of_cantor MeasureTheory.volume

def halfminus := λ n ↦ ite (n=0) false true
def halfplus  := λ n ↦ ite (n=0) true false

lemma halfplus_ne_halfminus : halfplus ≠ halfminus := by
  intro hc
  have : true = false := calc
    true = halfplus 0  := rfl
    _    = halfminus 0 := by rw [hc];
    _    = false       := rfl
  tauto

lemma real_of_cantor_noninjective :
  real_of_cantor halfminus = real_of_cantor halfplus := by
          have h₀: real_of_cantor halfminus = 1/2 := by
            unfold real_of_cantor halfminus
            simp
            let Q := @tsum_eq_add_tsum_ite
              ℝ ℕ _ _ _ (λ n ↦ (2 ^ (n+1))⁻¹) _ _ (by
                let S := geom_summable;simp at S;exact S
              ) 0
            simp at Q
            suffices (
              2⁻¹ + (∑' (n : ℕ), if n = 0 then 0 else ((2:ℝ) ^ (n + 1))⁻¹)
              = 2⁻¹ + 2⁻¹
            ) by apply add_left_cancel; exact this
            rw [← Q]
            let X := geom_value;simp at X;rw [X];ring_nf
          have h₁: real_of_cantor halfplus = 1/2 := by
            unfold real_of_cantor halfplus
            simp
            have : (∑' (n : ℕ), if n = 0 then ((2:ℝ) ^ (n + 1))⁻¹ else 0)
                 = (∑' (n : ℕ), if n = 0 then (2 ^ (0 + 1))⁻¹ else 0) := by
                  congr;apply funext;intro x;split_ifs with H
                  . subst H;rfl
                  . rfl
            have : (∑' (n : ℕ), if n = 0 then ((2:ℝ) ^ (n + 1))⁻¹ else 0)
              = (2 ^ (0 + 1))⁻¹ := by rw [this];exact tsum_ite_eq 0 (2 ^ (0 + 1))⁻¹
            rw [this]
            ring
          exact Eq.trans h₀ h₁.symm

lemma because_real_of_cantor_not_injective : CantorLebesgueMeasure Set.univ = 0 := by
  unfold CantorLebesgueMeasure
  unfold MeasureTheory.Measure.comap
  split_ifs with H
  . simp
    exfalso
    let Q := H.1 real_of_cantor_noninjective
    exact halfplus_ne_halfminus Q.symm
  . contrapose H
    simp
    simp at H
