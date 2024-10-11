import Mathlib.MeasureTheory.Measure.Hausdorff
import Marginis.Pathak2009
import KolmogorovExtension4.ProductMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
/-

# Randomness and Solovay degrees
by

## Miyabe, Nies, Stephan

JLA, 2018. Page 3 says:

`We sometimes identify a real α with its binary expansion X ∈ 2^ω`
`and the corresponding set X = {n ∈ ℕ : X (n) = 1 }`

Here we prove the well known fact that this representation is not unique.

We also show that consequently, if we use `Mathlib`'s current definition of
the pullback measure as of June 23, 2024 as a basis for a measure on Cantor space,
the Cantor space gets measure 0.

However, if we use Etienne Marion's KolmogorovExtension4 library
thinks work out well.
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
      exact @summable_geometric_of_norm_lt_one
                ℝ _ _ (1/2) (by simp; exact two_inv_lt_one)


noncomputable def CantorLebesgueMeasure₀ : MeasureTheory.Measure (ℕ → Bool) :=
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

lemma because_real_of_cantor_not_injective : CantorLebesgueMeasure₀ Set.univ = 0 := by
  unfold CantorLebesgueMeasure₀
  unfold MeasureTheory.Measure.comap
  split_ifs with H
  . simp
    exfalso
    let Q := H.1 real_of_cantor_noninjective
    exact halfplus_ne_halfminus Q.symm
  . contrapose H
    simp
    simp at H

open Classical

noncomputable instance fairCoin : PMF Bool := {
  val := fun b => (1:ENNReal)/2
  property := by
    have h₀ :=  @hasSum_fintype ENNReal Bool _ _ _ (fun b => 1/2)
    have h₁ : ∑ b : Bool, (1:ENNReal)/2 = 1 := by
      simp
      field_simp
      refine (ENNReal.div_eq_one_iff ?hb₀ ?hb₁).mpr rfl
      simp
      simp
    aesop
}

noncomputable def β : MeasureTheory.ProbabilityMeasure Bool := {
  val := fairCoin.toMeasure
  property := PMF.toMeasure.isProbabilityMeasure fairCoin
}

instance (n : ℕ) : MeasureTheory.IsProbabilityMeasure ((fun _ ↦ β.val) n) := by
  simp
  exact β.property

example : @MeasureTheory.Measure.infinitePiNat (fun _ : ℕ => Bool) _
    (fun _ => β.val) (fun _ => β.property)
    Set.univ = 1 := by
    simp only [
      MeasureTheory.ProbabilityMeasure.val_eq_to_measure,
      MeasureTheory.measure_univ
    ]

lemma fairValue (b : Bool) : fairCoin b = 1/2 := by
  unfold fairCoin
  show (fun b : Bool => (1:ENNReal)/2) true = 1/2
  simp

lemma fairSingleton (b : Bool) : β {b} = 1/2 := by
  unfold β
  simp
  have := fairValue b
  cases b
  simp_all
  rfl
  simp_all
  rfl

noncomputable def μFair := @MeasureTheory.productMeasure Nat (fun _ => Bool)
    _ (fun _ => β) _

instance : MeasureTheory.IsProbabilityMeasure μFair := by
  refine MeasureTheory.isProbabilityMeasure_iff.mpr ?_
  unfold μFair
  exact MeasureTheory.measure_univ

lemma fairUniv: μFair Set.univ = 1 := MeasureTheory.measure_univ

lemma fairHalf (b : Bool) (k : ℕ) : μFair {A | A k = b} = 1/2 := by
      have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
        (fun _ => β) _ {k} (fun i => {b}) (by simp)
      simp_all
      unfold Function.eval at h₀
      have h₂ : {f : ℕ → Bool | f k = b} = ((fun f ↦ f k) ⁻¹' {b}) := by aesop
      rw [← h₂] at h₀
      unfold μFair
      rw [h₀]
      have nnreal := fairSingleton b
      simp_all
      clear h₀
      clear h₂
      have : (β {b} : NNReal) = (2⁻¹ : NNReal) := nnreal
      have g₀ : (β {b} : ENNReal) = (2⁻¹ : ENNReal) := by aesop
      rw [← g₀]
      simp


/-- This mostly characterizes the measure. -/
lemma fairBoxes {s : ℕ} (b : Fin s → Bool) : μFair {A | ∀ k : Fin s, A k.1 = b k} = (1/2)^s := by
  have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
    (fun _ => β) _ {k < s | true}
    (fun k => dite (k < s) (fun h => {b ⟨k,h⟩}) (fun _ => Set.univ))
    (by simp)
  unfold μFair
  have g₀ : (MeasureTheory.productMeasure fun x ↦ β.toMeasure)
    ((Set.Iio s).pi fun k ↦ if h : k < s then {b ⟨k, h⟩} else {false, true})
          = (MeasureTheory.productMeasure fun x ↦ β.toMeasure)
    {A | ∀ (k : Fin s), A k.1 = b k} := by
    congr
    ext A
    simp
    constructor
    aesop
    intro h
    intro i hi
    have := h ⟨i,hi⟩
    simp_all

  have g₁ : ∏ x ∈ Finset.Iio s, β.toMeasure
    (if h : x < s then {b ⟨x, h⟩} else {false, true}) = ((1:ENNReal)/2)^s := by
    have g₂: ∀  x ∈ Finset.Iio s, β.toMeasure
      (if h : x < s then {b ⟨x, h⟩} else {false, true})
      = 1/2 := by
      intro x hx;
      split_ifs with j₀
      have := fairSingleton <|b ⟨x, j₀⟩
      clear g₀ h₀ hx
      unfold β
      aesop
      cases b ⟨x, j₀⟩
      aesop
      rw [fairValue]
      aesop
      simp
      rw [fairValue]
      simp
      unfold β
      aesop
    have g₃ : ∏ x ∈ Finset.Iio s, ((1:ENNReal)/2) = (1/2)^s := by
      have := @Finset.prod_const ℕ ENNReal (Finset.Iio s) _ (1/2)
      rw [this]
      congr
      exact Nat.card_Iio s
    rw [← g₃]
    exact Finset.prod_congr rfl g₂
  rw [← g₀]
  rw [← g₁]
  simp_all


instance γ : Group Bool := {
    mul := xor
    mul_assoc := fun a b c => by
        show xor (xor a b) c = xor a (xor b c)
        simp only [Bool.bne_assoc]
    one := false
    one_mul := fun a => by
        show xor false a = a
        simp
    mul_one := fun a => by
        show xor a false = a
        simp
    inv := fun a => a
    inv_mul_cancel := fun a => by
        show xor a a = false
        simp
}

instance : TopologicalGroup (ℕ → Bool) := TopologicalGroup.mk

noncomputable def ν := MeasureTheory.Measure.haarMeasure
    {
        carrier := (Set.univ : Set (ℕ → Bool))
        isCompact' := CompactSpace.isCompact_univ
        interior_nonempty' := by simp
    }

example : Unit := by
  have h₀: ν Set.univ = 1 := by
    apply MeasureTheory.Measure.haarMeasure_self
  have h₁: ν ∅ = 0 := MeasureTheory.OuterMeasureClass.measure_empty ν
  have h₂: {A | A 0 = false} ∪ {A | A 0 = true} = (Set.univ : Set (ℕ → Bool)) := by
    aesop
  have h₃: {A | A 0 = false} ∩ {A | A 0 = true} = (∅ : Set (ℕ → Bool)) := by
    aesop
  have h₄ : ν ({A | A 0 = false} ∪ {A | A 0 = true}) + ν ({A | A 0 = false} ∩ {A | A 0 = true}) =
  ν {A | A 0 = false} + ν {A | A 0 = true}
   := by
    refine MeasureTheory.measure_union_add_inter' ?hs {A : ℕ → Bool | A 0 = true}
    refine measurableSet_eq_fun_of_countable ?hs.hf ?hs.hg
    exact measurable_pi_apply 0
    exact measurable_const
  have h₅ : 1 + 0 =
  ν {A | A 0 = false} + ν {A | A 0 = true}
   := by
   aesop

  have h₆ : ν {A | A 0 = false} = ν {A | A 0 = true}
     := by
    -- use translation invariance
    have : MeasureTheory.Measure.IsMulLeftInvariant ν := by
        unfold ν
        exact
          MeasureTheory.Measure.isMulLeftInvariant_haarMeasure
            { carrier := Set.univ, isCompact' := ν.proof_2, interior_nonempty' := ν.proof_3 }
    unfold MeasureTheory.Measure.IsMulLeftInvariant at this
    -- unfold ν at this
    have := this.map_mul_left_eq_self (fun n => ite (n=0) true false)
    simp at this
    nth_rewrite 1 [← this]

    show (MeasureTheory.Measure.map
        (fun x ↦
            (fun n ↦ decide (n = 0)) * x
        ) ν) {A | A 0 = false}
        = ν {A | A 0 = true}
    show (MeasureTheory.Measure.map
        (fun x ↦
            (fun n ↦ decide (n = 0)) * fun n => x n
        ) ν) {A | A 0 = false}
        = ν {A | A 0 = true}
    show (MeasureTheory.Measure.map
        (fun x ↦
            (fun n ↦ xor (decide (n = 0)) (x n))
        ) ν) {A | A 0 = false}
        = ν {A | A 0 = true}
    have : {A : ℕ → Bool | A 0 = true} =
        {A | (fun x ↦
            (fun n ↦ xor (decide (n = 0)) (x n))
        ) A 0 = false} := by aesop
    rw [this]
    let f := (fun x : ℕ → Bool ↦
            (fun n ↦ xor (decide (n = 0)) (x n))
        )
    have (S : Set (ℕ → Bool)) (h :  MeasurableSet S) :  (MeasureTheory.Measure.map f ν) S
        = ν { A | f A ∈ S} := by
        rw [MeasureTheory.Measure.map_apply]
        congr

        · unfold f; exact Measurable.const_div (fun ⦃t⦄ a ↦ a) fun n ↦ decide (n = 0)
        · exact h
    show (MeasureTheory.Measure.map f ν) {A | A 0 = false}
        = ν {A | f A 0 = false}
    apply this
    refine measurableSet_eq_fun_of_countable ?h.hf ?h.hg
    exact measurable_pi_apply 0
    exact measurable_const
  have h₇ : ν {A | A 0 = true} = 1/2 := by
    rw [h₆] at h₅
    simp at h₅
    rw [h₅]
    ring_nf
    norm_cast
    symm
    have := @mul_div ENNReal _ (ν {A | A 0 = true}) 2 2
    rw [← this]
    ring_nf
    have : (2 : ENNReal) / 2 = 1 := by
        refine (ENNReal.div_eq_one_iff ?hb₀ ?hb₁).mpr rfl
        exact Ne.symm (NeZero.ne' 2)
        exact ENNReal.two_ne_top
    rw [this]
    simp
  exact PUnit.unit
