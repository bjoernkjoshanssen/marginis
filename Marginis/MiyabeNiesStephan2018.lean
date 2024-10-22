import Mathlib.MeasureTheory.Measure.Hausdorff
import Marginis.Pathak2009
import KolmogorovExtension4.ProductMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
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

set_option maxHeartbeats 2000000

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

/-- October 22: This is literally PMF.bernoulli p h -/
noncomputable def coin (p : NNReal) (h : p ≤ 1) : PMF Bool := {
  val := fun b => ite b p (1-p)
  property := by
    have h₀ :=  @hasSum_fintype ENNReal Bool _ _ _ fun b => ite b p (1-p)
    aesop
}



noncomputable def fairCoin' : PMF Bool := coin (1/2) (by simp)

noncomputable def fairCoin'' : PMF Bool := PMF.bernoulli (1/2) (by simp)

noncomputable def fairCoin : PMF Bool := {
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

theorem fairCoin_characterize : fairCoin = fairCoin' := by
  unfold fairCoin fairCoin'
  ext b
  congr
  simp

noncomputable def β : MeasureTheory.ProbabilityMeasure Bool := {
  val := fairCoin.toMeasure
  property := PMF.toMeasure.isProbabilityMeasure _
}

noncomputable def β' : MeasureTheory.ProbabilityMeasure Bool := {
  val := fairCoin''.toMeasure
  property := PMF.toMeasure.isProbabilityMeasure _
}


/-- Bernoulli measure. -/
noncomputable def βmeasure (p : NNReal) (hp : p ≤ 1) : MeasureTheory.ProbabilityMeasure Bool := {
  val := (coin p hp).toMeasure
  property := PMF.toMeasure.isProbabilityMeasure _
}

noncomputable def β'measure (p : ENNReal) (hp : p ≤ 1) : MeasureTheory.ProbabilityMeasure Bool := {
  val := (@PMF.bernoulli p hp).toMeasure
  property := PMF.toMeasure.isProbabilityMeasure _
}


instance (n : ℕ)  (p : NNReal) (hp : p ≤ 1) : MeasureTheory.IsProbabilityMeasure
    ((fun _ ↦ (βmeasure p hp).val) n) := by
  simp
  exact (βmeasure p hp).property


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

lemma fairValue (b : Bool) : fairCoin b = 1/2 := rfl

lemma fairValue'' (b : Bool) : fairCoin'' b = 1/2 := by
  unfold fairCoin''
  simp

lemma bernoulliValueTrue (p : NNReal) (hp : p ≤ 1) :
    coin p hp true = p := rfl

lemma bernoulliValueTrue'' (p : ENNReal) (hp : p ≤ 1) :
    PMF.bernoulli p hp true = p := rfl

lemma bernoulliValueFalse (p : NNReal) (hp : p ≤ 1) :
    coin p hp false = 1 - p := rfl

lemma bernoulliValueFalse'' (p : ENNReal) (hp : p ≤ 1) :
    PMF.bernoulli p hp false = 1 - p := rfl

lemma bernoulliSingletonTrue (p : NNReal) (hp : p ≤ 1) :
    βmeasure p hp {true} = p := by
  unfold βmeasure
  simp
  have := bernoulliValueTrue p hp
  simp_all

lemma bernoulliSingletonTrue'' (p : ENNReal) (hp : p ≤ 1) :
    β'measure p hp {true} = p := by
  unfold β'measure
  simp
  refine ENNReal.coe_toNNReal ?_
  aesop

lemma bernoulliSingletonFalse'' (p : ENNReal) (hp : p ≤ 1) :
    β'measure p hp {false} = 1-p := by
  unfold β'measure
  simp

lemma bernoulliSingletonFalse (p : NNReal) (hp : p ≤ 1) :
    βmeasure p hp {false} = 1 - p := by
  unfold βmeasure
  simp
  have := bernoulliValueFalse p hp
  aesop

lemma fairSingleton'' (b : Bool) : β' {b} = 1/2 := by
  unfold β'
  simp
  have := fairValue'' b
  cases b
  simp_all
  rfl
  simp_all
  rfl


lemma fairSingleton (b : Bool) : β {b} = 1/2 := by
  unfold β
  simp
  have := fairValue b
  cases b
  simp_all
  rfl
  simp_all
  rfl

noncomputable def μBernoulli'' (p : ENNReal) (hp : p ≤ 1) :=
    @MeasureTheory.productMeasure Nat (fun _ => Bool)
    _ (fun _ => β'measure p hp) _

noncomputable def μBernoulli (p : NNReal) (hp : p ≤ 1) :=
    @MeasureTheory.productMeasure Nat (fun _ => Bool)
    _ (fun _ => βmeasure p hp) _

instance (p : NNReal) (hp : p ≤ 1) :
    MeasureTheory.IsProbabilityMeasure <|μBernoulli p hp := by
  refine MeasureTheory.isProbabilityMeasure_iff.mpr ?_
  unfold μBernoulli
  exact MeasureTheory.measure_univ

instance (p : ENNReal) (hp : p ≤ 1) :
    MeasureTheory.IsProbabilityMeasure <|μBernoulli'' p hp := by
  refine MeasureTheory.isProbabilityMeasure_iff.mpr ?_
  unfold μBernoulli''
  exact MeasureTheory.measure_univ

lemma bernoulliUniv (p : NNReal) (hp : p ≤ 1) :
    μBernoulli p hp Set.univ = 1 := MeasureTheory.measure_univ

lemma bernoulliUniv'' (p : ENNReal) (hp : p ≤ 1) :
    μBernoulli'' p hp Set.univ = 1 := MeasureTheory.measure_univ

noncomputable def μFair := @MeasureTheory.productMeasure Nat (fun _ => Bool)
    _ (fun _ => β) _

noncomputable def μFair'' := @MeasureTheory.productMeasure Nat (fun _ => Bool)
    _ (fun _ => β') _

instance : MeasureTheory.IsProbabilityMeasure μFair := by
  refine MeasureTheory.isProbabilityMeasure_iff.mpr ?_
  unfold μFair
  exact MeasureTheory.measure_univ

instance : MeasureTheory.IsProbabilityMeasure μFair'' := by
  refine MeasureTheory.isProbabilityMeasure_iff.mpr ?_
  unfold μFair''
  exact MeasureTheory.measure_univ

lemma fairUniv: μFair Set.univ = 1 := MeasureTheory.measure_univ

lemma fairUniv'': μFair'' Set.univ = 1 := MeasureTheory.measure_univ

lemma trueμBernoulli'' (p : ENNReal) (hp : p ≤ 1) (k : ℕ) :
    μBernoulli'' p hp {A | A k = true} = p := by
  have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
    (fun _ => β'measure p hp) _ {k} (fun i => {true}) (by simp)
  simp at h₀
  have h₂ : {f : ℕ → Bool | f k = true} = ((fun f ↦ f k) ⁻¹' {true}) := by aesop
  rw [← h₂] at h₀
  unfold μBernoulli''
  rw [h₀]
  have := bernoulliSingletonTrue'' p hp
  have g₀ : (β'measure p hp {true} ) = p := by aesop
  simp_all


lemma trueμBernoulli (p : NNReal) (hp : p ≤ 1) (k : ℕ) :
    μBernoulli p hp {A | A k = true} = p := by
  have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
    (fun _ => βmeasure p hp) _ {k} (fun i => {true}) (by simp)
  simp at h₀
  have h₂ : {f : ℕ → Bool | f k = true} = ((fun f ↦ f k) ⁻¹' {true}) := by aesop
  rw [← h₂] at h₀
  unfold μBernoulli
  rw [h₀]
  have := bernoulliSingletonTrue p hp
  have g₀ : (βmeasure p hp {true} : ENNReal) = p := by aesop
  rw [← g₀]
  simp


lemma falseμBernoulli'' (p : ENNReal) (hp : p ≤ 1) (k : ℕ) :
    μBernoulli'' p hp {A | A k = false} = 1 - p := by
  have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
    (fun _ => β'measure p hp) _ {k} (fun i => {false}) (by simp)
  simp at h₀
  have h₂ : {f : ℕ → Bool | f k = false} = ((fun f ↦ f k) ⁻¹' {false}) := by aesop
  rw [← h₂] at h₀
  unfold μBernoulli''
  rw [h₀]
  have := bernoulliSingletonFalse'' p hp
  have g₀ : β'measure p hp {false} = 1 - p := by aesop
  simp_all

lemma falseμBernoulli (p : NNReal) (hp : p ≤ 1) (k : ℕ) :
    μBernoulli p hp {A | A k = false} = 1 - p := by
  have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
    (fun _ => βmeasure p hp) _ {k} (fun i => {false}) (by simp)
  simp at h₀
  have h₂ : {f : ℕ → Bool | f k = false} = ((fun f ↦ f k) ⁻¹' {false}) := by aesop
  rw [← h₂] at h₀
  unfold μBernoulli
  rw [h₀]
  have := bernoulliSingletonFalse p hp
  have g₀ : (βmeasure p hp {false} : ENNReal) = 1 - p := by aesop
  rw [← g₀]
  simp

lemma fairHalf (b : Bool) (k : ℕ) : μFair {A | A k = b} = 1/2 := by
      have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
        (fun _ => β) _ {k} (fun i => {b}) (by simp)
      simp at h₀
      have h₂ : {f : ℕ → Bool | f k = b} = ((fun f ↦ f k) ⁻¹' {b}) := by aesop
      rw [← h₂] at h₀
      unfold μFair
      rw [h₀]
      have := fairSingleton b
      have g₀ : (β {b} : ENNReal) = (1/2 : ENNReal) := by aesop
      rw [← g₀]
      simp

open Finset

/-- Progress since this one is based on PMF.bernoulli -/
lemma bernoulliBoxes'' {s : ℕ} (b : Fin s → Bool) (p : ENNReal) (hp : p ≤ 1) :
    ∏ x ∈ Iio s, (β'measure p hp).toMeasure
    (if h : x < s then {b ⟨x, h⟩} else {false, true})
    = p^ card {t | b t = true} * (1-p) ^ card {t | b t = false} := by
    have g₂: ∀  x ∈ Iio s, (β'measure p hp).toMeasure
        (if h : x < s then {b ⟨x, h⟩} else {false, true})
        = if h : x < s then PMF.bernoulli p hp (b ⟨x,h⟩) else 1 := by
      intro x hx
      split_ifs with j₀
      unfold β'measure
      cases b ⟨x, j₀⟩ <;> aesop
      aesop
    have g₃ : ∏ _ ∈ Iio s, p = p^s := by
      have := @prod_const ℕ ENNReal (Iio s) _ p
      aesop
    have g₄ : ∏ _ ∈ Iio s, (1 - p) = (1 - p)^s := by
      have := @prod_const ℕ ENNReal (Iio s) _ (1 - p)
      aesop
    have QQ := @prod_union ℕ ENNReal (filter (fun t =>
            dite (t < s) (fun h => b ⟨t,h⟩ = true) (fun _ => true)
        ) (Iio s)) (filter (fun t =>
            dite (t < s) (fun h => b ⟨t,h⟩ = false) (fun _ => true)
        ) (Iio s)) (fun x => if h : x < s then PMF.bernoulli p hp (b ⟨x,h⟩) else 1) _ _ (by
            intro S hst hsf x hxs
            have Qt := hst hxs
            have Qf := hsf hxs
            simp at Qt Qf
            exfalso
            clear hst hsf g₃ g₄ g₂ hp p
            aesop
        )
    simp at QQ
    unfold β'measure
    have QQ₀ : (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = true) (Iio s),
      if h : x < s then (PMF.bernoulli p hp) (b ⟨x, h⟩) else 1) =
      (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = true) (Iio s),
      if x < s then (p : ENNReal) else 1)
      := by
        refine prod_bijective id Function.bijective_id ?hst ?hfg
        intro i
        simp
        intro i hi
        simp at hi
        simp
        split_ifs with j
        rw [hi.2 j]
        rfl
        rfl
    have QQ₁ : (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s),
      if h : x < s then (PMF.bernoulli p hp) (b ⟨x, h⟩) else 1) =
      (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s),
      if h : x < s then (1 - p : ENNReal) else 1) := by
        apply prod_bijective id Function.bijective_id
        intro i
        simp
        intro i hi
        simp at hi
        simp
        split_ifs with j
        rw [hi.2 j]
        rfl
        rfl
    unfold PMF.bernoulli at QQ₀ QQ₁
    simp at QQ₀ QQ₁
    rw [QQ₀, QQ₁] at QQ
    have : Iio s =
        filter (fun t => dite (t < s) (fun h => b ⟨t,h⟩ =  true) (fun _ => true)) (Iio s)
        ∪
        filter (fun t => dite (t < s) (fun h => b ⟨t,h⟩ = false) (fun _ => true)) (Iio s)
        := by aesop
    simp at this
    rw [← this] at QQ
    -- simp at QQ
    have T (z : Bool) (q : ENNReal) :
        (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s), if x < s then q else 1)
      = (∏ _ ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s),  ↑q) := by
        apply prod_bijective id Function.bijective_id
        intro i
        simp
        intro i hi
        simp at hi
        simp
        intro;exfalso;linarith
    have T₁ :
        (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s), if x < s then (1 - p) else 1)
      = (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s),  (1 - p)) := by
            apply prod_bijective id Function.bijective_id
            · intro i
              simp
            · intro i hi
              simp at hi
              simp
              intro;exfalso;linarith
    rw [T true p, T₁] at QQ
    simp at QQ
    have Y (z : Bool) : (filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s)).card
            = (filter (fun t ↦ b t = z) univ).card := by
        apply card_bij (fun (a : ℕ)
            (ha : a ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s))
            => ⟨a,by simp at ha;tauto⟩)
        intro a ha
        simp
        simp at ha
        tauto
        intro a₁ ha₁ a₂ ha₂ h
        simp at h
        tauto
        intro k hk;simp at hk;simp;use k.1;use ⟨k.2,by tauto⟩
    rw [← Y true, ← Y false, ← QQ]
    apply prod_bijective id Function.bijective_id
    · simp
    · intro i hi
      simp at hi
      simp
      split_ifs with j
      · cases b ⟨i,j⟩ <;> simp
      · cases b ⟨i,hi⟩ <;> simp


/-- Not the simplest form of what we want to prove -/
lemma bernoulliBoxes' {s : ℕ} (b : Fin s → Bool) (p : NNReal) (hp : p ≤ 1) :
    ∏ x ∈ Iio s, (βmeasure p hp).toMeasure
    (if h : x < s then {b ⟨x, h⟩} else {false, true})
    = p^ card {t | b t = true} * (1-p) ^ card {t | b t = false} := by
    have g₂: ∀  x ∈ Iio s, (βmeasure p hp).toMeasure
        (if h : x < s then {b ⟨x, h⟩} else {false, true})
        = if h : x < s then coin p hp (b ⟨x,h⟩) else 1 := by
      intro x hx
      split_ifs with j₀
      unfold βmeasure
      cases b ⟨x, j₀⟩ <;> aesop
      aesop
    have g₃ : ∏ _ ∈ Iio s, p = p^s := by
      have := @prod_const ℕ ENNReal (Iio s) _ p
      aesop
    have g₄ : ∏ _ ∈ Iio s, (1 - p) = (1 - p)^s := by
      have := @prod_const ℕ ENNReal (Iio s) _ (1 - p)
      aesop
    have QQ := @prod_union ℕ ENNReal (filter (fun t =>
            dite (t < s) (fun h => b ⟨t,h⟩ = true) (fun _ => true)
        ) (Iio s)) (filter (fun t =>
            dite (t < s) (fun h => b ⟨t,h⟩ = false) (fun _ => true)
        ) (Iio s)) (fun x => if h : x < s then coin p hp (b ⟨x,h⟩) else 1) _ _ (by
            intro S hst hsf x hxs
            have Qt := hst hxs
            have Qf := hsf hxs
            simp at Qt Qf
            exfalso
            clear hst hsf g₃ g₄ g₂ hp p
            aesop
        )
    simp at QQ
    unfold βmeasure
    have QQ₀ : (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = true) (Iio s),
      if h : x < s then (coin p hp) (b ⟨x, h⟩) else 1) =
      (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = true) (Iio s),
      if x < s then (p : ENNReal) else 1)
      := by
        refine prod_bijective id Function.bijective_id ?hst ?hfg
        intro i
        simp
        intro i hi
        simp at hi
        simp
        split_ifs with j
        rw [hi.2 j]
        rfl
        rfl
    have QQ₁ : (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s),
      if h : x < s then (coin p hp) (b ⟨x, h⟩) else 1) =
      (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s),
      if h : x < s then (1 - p : ENNReal) else 1) := by
        apply prod_bijective id Function.bijective_id
        intro i
        simp
        intro i hi
        simp at hi
        simp
        split_ifs with j
        rw [hi.2 j]
        rfl
        rfl
    rw [QQ₀, QQ₁] at QQ
    have : Iio s =
        filter (fun t => dite (t < s) (fun h => b ⟨t,h⟩ =  true) (fun _ => true)) (Iio s)
        ∪
        filter (fun t => dite (t < s) (fun h => b ⟨t,h⟩ = false) (fun _ => true)) (Iio s)
        := by aesop
    simp at this
    rw [← this] at QQ
    simp at QQ
    have T (z : Bool) (q : NNReal) :
        (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s), if x < s then ENNReal.ofNNReal q else 1)
      = (∏ _ ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s),  ↑q) := by
        apply prod_bijective id Function.bijective_id
        intro i
        simp
        intro i hi
        simp at hi
        simp
        intro;exfalso;linarith
    have T₁ :
        (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s), if x < s then (1 - ENNReal.ofNNReal p) else 1)
      = (∏ x ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = false) (Iio s),  (1 - ENNReal.ofNNReal p)) := by
            apply prod_bijective id Function.bijective_id
            · intro i
              simp
            · intro i hi
              simp at hi
              simp
              intro;exfalso;linarith
    rw [T true p, T₁] at QQ
    simp at QQ
    have Y (z : Bool) : (filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s)).card
            = (filter (fun t ↦ b t = z) univ).card := by
        apply card_bij (fun (a : ℕ)
            (ha : a ∈ filter (fun t ↦ ∀ (h : t < s), b ⟨t, h⟩ = z) (Iio s))
            => ⟨a,by simp at ha;tauto⟩)
        intro a ha
        simp
        simp at ha
        tauto
        intro a₁ ha₁ a₂ ha₂ h
        simp at h
        tauto
        intro k hk;simp at hk;simp;use k.1;use ⟨k.2,by tauto⟩
    rw [← Y true, ← Y false, ← QQ]
    apply prod_bijective id Function.bijective_id
    · simp
    · intro i hi
      simp at hi
      simp
      split_ifs with j
      · cases b ⟨i,j⟩ <;> simp
      · cases b ⟨i,hi⟩ <;> simp

/-- Basic fact about Bernoulli measure on 2^ℕ. -/
theorem bernoulliBoxes {s : ℕ} (b : Fin s → Bool) (p : NNReal) (hp : p ≤ 1) :
    μBernoulli p hp {A : ℕ → Bool | ∀ (k : Fin s), A k.1 = b k}
    = p^ card {t | b t = true} * (1-p) ^ card {t | b t = false} := by
    unfold μBernoulli
    have g₀ : (MeasureTheory.productMeasure fun _ ↦ (βmeasure p hp).toMeasure)
        ((Set.Iio s).pi fun k ↦ if h : k < s then {b ⟨k, h⟩} else {false, true})
            = (MeasureTheory.productMeasure fun _ ↦ (βmeasure p hp).toMeasure)
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
    have h := bernoulliBoxes' b p hp
    rw [← h]
    have := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
        (fun _ => βmeasure p hp) _ (Iio s)
        (fun k => dite (k < s) (fun h => {b ⟨k,h⟩}) (fun _ => Set.univ))
        (by simp)
    simp_all

/-- October 22 -/
theorem bernoulliBoxes''' {s : ℕ} (b : Fin s → Bool) (p : ENNReal) (hp : p ≤ 1) :
    μBernoulli'' p hp {A : ℕ → Bool | ∀ (k : Fin s), A k.1 = b k}
    = p^ card {t | b t = true} * (1-p) ^ card {t | b t = false} := by
    unfold μBernoulli''
    have g₀ : (MeasureTheory.productMeasure fun _ ↦ (β'measure p hp).toMeasure)
        ((Set.Iio s).pi fun k ↦ if h : k < s then {b ⟨k, h⟩} else {false, true})
            = (MeasureTheory.productMeasure fun _ ↦ (β'measure p hp).toMeasure)
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
    have h := bernoulliBoxes'' b p hp
    rw [← h]
    have := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
        (fun _ => β'measure p hp) _ (Iio s)
        (fun k => dite (k < s) (fun h => {b ⟨k,h⟩}) (fun _ => Set.univ))
        (by simp)
    simp_all

lemma noAtomsReal (p ε : ℝ) (h₀ : 0 < p) (h₁ : p < 1) (h : 0 < ε) :
    ∃ n : ℕ, p^n ≤ ε := by
    use Nat.ceil <|Real.logb p ε
    have :  p ^ ⌈Real.logb p ε⌉₊ =  p ^ (⌈Real.logb p ε⌉₊ : ℝ) := by
        exact Eq.symm (Real.rpow_natCast p ⌈Real.logb p ε⌉₊)
    rw [this]
    have : Real.logb p ε ≤ (Nat.ceil (Real.logb p ε) : ℝ) := Nat.le_ceil (Real.logb p ε)
    calc _ ≤ p ^ Real.logb p ε := (Real.rpow_le_rpow_left_iff_of_base_lt_one h₀ h₁).mpr this
    _ = ε := by refine Real.rpow_logb h₀ ?b_ne_one h;aesop

lemma noAtomsNNReal (ε : NNReal) (p : ℝ) (h₀ : 0 < p) (h₁ : p < 1) (h : 0 < ε) :
    ∃ n : ℕ, p^n ≤ ε := by
  have := noAtomsReal p ε h₀ h₁ h
  tauto

lemma noAtomsENNReal (ε : ENNReal) (H : ε ≠ ⊤) (p : ℝ) (h₀ : 0 < p) (h₁ : p < 1) (h : 0 < ε) :
    ∃ n : ℕ, p^n ≤ ε.toReal := by
  have := noAtomsNNReal ε.toNNReal p h₀ h₁ (by
    refine ENNReal.toNNReal_pos ?ha₀ H
    aesop
  )
  aesop

theorem extracted_1 (B : ℕ → Bool) (p : NNReal) (hp : p ≤ 1) (ε : ENNReal)
  (n₀ : ℕ) (hn₀ : ↑p ^ n₀ ≤ ε.toReal) (n₁ : ℕ) (z : Bool) (m : ENNReal)
  (this : m ≤
            p ^ (filter (fun (t : Fin (2 * max n₀ n₁)) ↦ B t =  z) univ).card *
      (1 - p) ^ (filter (fun (t : Fin (2 * max n₀ n₁)) ↦ B t = !z) univ).card)
  (h : (filter (fun (t : Fin (2 * max n₀ n₁)) ↦ B ↑t = z) univ).card ≥ max n₀ n₁) :
  m ≤ ε := by
let M := max n₀ n₁
have h1p : 1 - (ENNReal.ofNNReal p) ≤ 1 := by aesop
calc
    _ ≤ _ := this
    _ ≤ (p:NNReal) ^ (filter (fun (t : Fin (2 * M)) ↦ B t = z) univ).card * 1 :=
        mul_le_mul (le_refl _) (by calc
        _ ≤  (1:ENNReal) ^ (filter (fun (t : Fin (2 * M)) ↦ B t = !z) univ).card :=
        pow_le_pow_left' h1p (filter (fun (t : Fin (2 * M)) ↦ B t = !z) univ).card
        _ ≤ _ := by aesop
        ) (by aesop) (by aesop)
    _ = p ^ (filter (fun (t : Fin (2 * M)) ↦ B t = z) univ).card := by simp
    _ ≤ _ := by calc
        _ ≤ (ENNReal.ofNNReal p) ^ M := by
            refine pow_le_pow_right_of_le_one' ?ha h
            exact ENNReal.coe_le_one_iff.mpr hp
        _ ≤ p ^ n₀ := by
            refine pow_le_pow_right_of_le_one' ?ha (by aesop)
        _ ≤ _ := by
            simp_all
            apply ENNReal.le_of_top_imp_top_of_toNNReal_le
            tauto
            tauto

theorem extracted_1' (B : ℕ → Bool) (p : ENNReal) (hp : p ≤ 1) (ε : ENNReal)
  (n₀ : ℕ) (hn₀ : p ^ n₀ ≤ ε) (n₁ : ℕ) (z : Bool) (m : ENNReal)
  (this : m ≤
            p ^ (filter (fun (t : Fin (2 * max n₀ n₁)) ↦ B t =  z) univ).card *
      (1 - p) ^ (filter (fun (t : Fin (2 * max n₀ n₁)) ↦ B t = !z) univ).card)
  (h : (filter (fun (t : Fin (2 * max n₀ n₁)) ↦ B ↑t = z) univ).card ≥ max n₀ n₁) :
  m ≤ ε := by
let M := max n₀ n₁
have h1p : 1 - (p) ≤ 1 := by aesop
calc
    _ ≤ _ := this
    _ ≤ (p) ^ (filter (fun (t : Fin (2 * M)) ↦ B t = z) univ).card * 1 :=
        mul_le_mul (le_refl _) (by calc
        _ ≤  (1:ENNReal) ^ (filter (fun (t : Fin (2 * M)) ↦ B t = !z) univ).card :=
        pow_le_pow_left' h1p (filter (fun (t : Fin (2 * M)) ↦ B t = !z) univ).card
        _ ≤ _ := by aesop
        ) (by aesop) (by aesop)
    _ = p ^ (filter (fun (t : Fin (2 * M)) ↦ B t = z) univ).card := by simp
    _ ≤ _ := by calc
        _ ≤ ( p) ^ M := by
            refine pow_le_pow_right_of_le_one' ?ha h
            exact hp
            --exact ENNReal.coe_le_one_iff.mpr hp
        _ ≤ p ^ n₀ := by
            refine pow_le_pow_right_of_le_one' ?ha (by aesop)
        _ ≤ _ := by
            simp_all

/-- Oct 22 2024. Needs serious golfing. -/
theorem bernoulliNoAtoms'' {p : ENNReal} (hp : p ≤ 1)
                       (hn₀ : 0 < p) (hn₁ : p < 1) (B : ℕ → Bool) :
    μBernoulli'' p hp {B} = 0 := by
  refine le_antisymm ?_
    (show 0 ≤ (MeasureTheory.productMeasure fun _ ↦ (β'measure p hp)) {B} by simp)
  apply le_of_forall_le_of_dense
  intro ε hε
  have (s : ℕ) : μBernoulli'' p hp {B} ≤
                 μBernoulli'' p hp {A | ∀ (k : Fin s), A k.1 = B k.1} :=
    MeasureTheory.OuterMeasureClass.measure_mono (μBernoulli'' p hp) (by aesop)
  have h₁ (s : ℕ) := bernoulliBoxes''' (fun k : Fin s => B k.1) p hp -- key!
  have h₂ : ∀ (s : ℕ), (μBernoulli'' p hp) {B} ≤
            p ^ (univ.filter fun t : Fin s ↦ B t =  true).card
    * (1 - p) ^ (univ.filter fun t : Fin s ↦ B t = false).card := by aesop
  by_cases H : ε = ⊤
  · aesop

  have htop : p ≠ ⊤ := by aesop
  have := @noAtomsENNReal ε H p.toReal (by

    refine ENNReal.toReal_pos ?ha₀ htop
    exact Ne.symm (ne_of_lt hn₀)
  ) (by
    clear h₂ h₁ hε H this B ε hp
    refine (ENNReal.lt_ofReal_iff_toReal_lt htop).mp ?_
    aesop
  ) hε
  obtain ⟨n₀,hn₀⟩ := this --noAtomsENNReal ε H p hn₀ hn₁ hε

  have := @noAtomsENNReal ε H (1-p).toReal (by

    apply ENNReal.toReal_pos
    have : 1 - 1 < 1 - p := by
      apply ENNReal.sub_lt_of_sub_lt
      simp
      left
      simp
      have : 1 - (1 - p) = p := by
        refine ENNReal.sub_sub_cancel ?h hp
        exact ENNReal.one_ne_top
      rw [this]
      tauto
    have : 0 < 1 - p := by aesop
    contrapose this
    simp at this
    rw [this]
    simp

    refine ENNReal.sub_ne_top ?ha_top.ha
    simp
  ) (by
    have : (1 - p).toReal = (1 : ENNReal).toReal - p.toReal := by
      refine ENNReal.toReal_sub_of_le hp ?ha
      simp
    rw [this]
    simp
    apply ENNReal.toReal_pos
    aesop
    tauto
  ) hε
  obtain ⟨n₁,hn₁⟩ := this --noAtomsENNReal ε H (1-p) (by aesop) (by aesop) hε
  let M := 2 * max n₀ n₁
  have h₀ : (univ.filter fun t : Fin M ↦ B t =  true).card ≥ max n₀ n₁ ∨
            (univ.filter fun t : Fin M ↦ B t = false).card ≥ max n₀ n₁ := by
        by_contra hc
        push_neg at hc
        have htf : (univ : Finset (Fin M))
            = univ.filter (fun t : Fin M => B t = true)
            ∪ univ.filter (fun t => B t = false) := by aesop
        have p₀: (univ : Finset (Fin M)).card < M := by
            rw [htf]
            calc
            _ ≤ _ := card_union_le (univ.filter fun t : Fin M => B t =  true)
                                   (univ.filter fun t : Fin M => B t = false)
            _ < _ := by unfold M;linarith
        rw [card_fin M] at p₀
        simp at p₀
  cases h₀ with
  | inl h =>
    exact extracted_1' B p hp ε n₀ (by
      clear this h₁ h₂ h M B hn₁ n₁
      have : p.toReal ^ n₀ = (p^n₀).toReal := by
        exact Eq.symm (ENNReal.toReal_pow p n₀)
      rw [this] at hn₀
      clear this
      apply ENNReal.le_of_top_imp_top_of_toNNReal_le
      intro h;exfalso;simp at h;tauto
      intros
      aesop
    ) n₁ true  (μBernoulli'' p hp {B})
        (h₂ M) h
  | inr h =>
    exact extracted_1' B (1-p) (by aesop) ε n₁ (by
      have : (1-p).toReal ^ n₁ = ((1-p)^n₁).toReal := by
        exact Eq.symm (ENNReal.toReal_pow (1-p) n₁)
      rw [this] at hn₁
      apply ENNReal.le_of_top_imp_top_of_toNNReal_le
      intro h;exfalso;simp at h;tauto;
    ) n₀ false (μBernoulli'' p hp {B})
        (by
            simp;rw [mul_comm]
            have w₀: 1 - (1 -  p) = p := by
                apply ENNReal.sub_sub_cancel
                · simp
                · aesop
            rw [w₀]
            simp_all
        ) (by rw [max_comm];tauto)

/-- Oct 15 2024 -/
theorem bernoulliNoAtoms {p : NNReal} (hp : p ≤ 1)
                       (hn₀ : 0 < p) (hn₁ : p < 1) (B : ℕ → Bool) :
    μBernoulli p hp {B} = 0 := by
  refine le_antisymm ?_
    (show 0 ≤ (MeasureTheory.productMeasure fun _ ↦ (βmeasure p hp)) {B} by simp)
  apply le_of_forall_le_of_dense
  intro ε hε
  have (s : ℕ) : μBernoulli p hp {B} ≤
                 μBernoulli p hp {A | ∀ (k : Fin s), A k.1 = B k.1} :=
    MeasureTheory.OuterMeasureClass.measure_mono (μBernoulli p hp) (by aesop)
  have h₁ (s : ℕ) := bernoulliBoxes (fun k : Fin s => B k.1) p hp -- key!
  have h₂ : ∀ (s : ℕ), (μBernoulli p hp) {B} ≤
            p ^ (univ.filter fun t : Fin s ↦ B t =  true).card
    * (1 - p) ^ (univ.filter fun t : Fin s ↦ B t = false).card := by aesop
  by_cases H : ε = ⊤
  · aesop
  obtain ⟨n₀,hn₀⟩ := noAtomsENNReal ε H p hn₀ hn₁ hε
  obtain ⟨n₁,hn₁⟩ := noAtomsENNReal ε H (1-p) (by aesop) (by aesop) hε
  let M := 2 * max n₀ n₁
  have h₀ : (univ.filter fun t : Fin M ↦ B t =  true).card ≥ max n₀ n₁ ∨
            (univ.filter fun t : Fin M ↦ B t = false).card ≥ max n₀ n₁ := by
        by_contra hc
        push_neg at hc
        have htf : (univ : Finset (Fin M))
            = univ.filter (fun t : Fin M => B t = true)
            ∪ univ.filter (fun t => B t = false) := by aesop
        have p₀: (univ : Finset (Fin M)).card < M := by
            rw [htf]
            calc
            _ ≤ _ := card_union_le (univ.filter fun t : Fin M => B t =  true)
                                   (univ.filter fun t : Fin M => B t = false)
            _ < _ := by unfold M;linarith
        rw [card_fin M] at p₀
        simp at p₀
  cases h₀ with
  | inl h =>
    exact extracted_1 B    p          hp ε n₀        hn₀ n₁ true  (μBernoulli p hp {B})
        (h₂ M) h
  | inr h =>
    exact extracted_1 B (1-p) (by aesop) ε n₁ (by aesop) n₀ false (μBernoulli p hp {B})
        (by
            simp;rw [mul_comm]
            have w₀: 1 - (1 - ENNReal.ofNNReal p) = p := by
                apply ENNReal.sub_sub_cancel
                · simp
                · aesop
            rw [w₀]
            simp_all
        ) (by rw [max_comm];tauto)

instance (p : NNReal) (hp : p ≤ 1) (h₀ : 0 < p) (h₁ : p < 1) :
    MeasureTheory.NoAtoms <|μBernoulli p hp := {
    measure_singleton := bernoulliNoAtoms hp h₀ h₁
}

/-- This mostly characterizes the measure. -/
lemma fairBoxes {s : ℕ} (b : Fin s → Bool) : μFair {A | ∀ k : Fin s, A k.1 = b k} = (1/2)^s := by
/- Can also prove it like this:
  have := @bernoulliBoxes s b (1/2) (by aesop)
  unfold μFair β fairCoin
  unfold μBernoulli βmeasure coin at this
  simp_all
  ring_nf
  have : (2:ENNReal)⁻¹ ^ (filter (fun t ↦ b t = true) univ).card * 2⁻¹ ^ (filter (fun t ↦ b t = false) univ).card
   = 2⁻¹ ^ ((filter (fun t ↦ b t = true) univ).card + (filter (fun t ↦ b t = false) univ).card) := by
    rw [pow_add]
  rw [this]
  congr
  have : s = (univ : Finset (Fin s)).card := by aesop
  simp_rw [this]
  etc.
  -/

  have h₀ := @MeasureTheory.productMeasure_boxes ℕ (fun _ => Bool) _
    (fun _ => β) _ (Iio s)
    (fun k => dite (k < s) (fun h => {b ⟨k,h⟩}) (fun _ => Set.univ))
    (by simp)
  unfold μFair
  have g₀ : (MeasureTheory.productMeasure fun _ ↦ β.toMeasure)
    ((Set.Iio s).pi fun k ↦ if h : k < s then {b ⟨k, h⟩} else {false, true})
          = (MeasureTheory.productMeasure fun _ ↦ β.toMeasure)
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

  have g₁ : ∏ x ∈ Iio s, β.toMeasure
    (if h : x < s then {b ⟨x, h⟩} else {false, true}) = ((1:ENNReal)/2)^s := by
    have g₂: ∀  x ∈ Iio s, β.toMeasure
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
    have g₃ : ∏ x ∈ Iio s, ((1:ENNReal)/2) = (1/2)^s := by
      have := @prod_const ℕ ENNReal (Iio s) _ (1/2)
      rw [this]
      congr
      exact Nat.card_Iio s
    rw [← g₃]
    exact prod_congr rfl g₂
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
  have : ν ∅ = 0 := MeasureTheory.OuterMeasureClass.measure_empty ν
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
  have : ν {A | A 0 = true} = 1/2 := by
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

example  (p : ENNReal) (hp : p ≤ 1) : Unit :=
  have := @PMF.bernoulli_expectation p hp
  sorry

example  (p : NNReal) (hp : p ≤ 1) :
    ProbabilityTheory.variance
    (fun A : Bool => ite (A) 1 0) (βmeasure p hp) = p * (1-p) := by
  unfold ProbabilityTheory.variance ProbabilityTheory.evariance βmeasure coin
  simp
  rw [MeasureTheory.lintegral]
  -- do a finite version of this instead of Nat → Bool
  sorry
