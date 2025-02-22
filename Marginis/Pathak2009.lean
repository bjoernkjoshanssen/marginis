import Mathlib.MeasureTheory.Measure.Haar.OfBasis
/-!

# A computational aspect of the Lebesgue differentiation theorem

[NOOPUR PATHAK](http://logicandanalysis.org/index.php/jla/article/view/28)

She writes
`Another characterization of random points in ℝ^d is given by Solovay's Lemma. [...]`
`The proof given by Simpson is given for sets in the Cantor space, but the proof applies here as well.`

Here we expound this by constructing the Cantor-Lebesgue measure on 2^ω using the Lebesgue measure on [0,1].

[
Related Marginis entries: Miyabe, Nies, Stephan: Randomness and Solovay degrees at
https://github.com/bjoernkjoshanssen/jla/blob/main/2018-miyabe-nies-stephan.lean
(proving that the usual map from 2^omega to [0,1] is not injective)
and
Pauly and Fouche at
https://github.com/bjoernkjoshanssen/jla/blob/main/2017-pauly-fouche.lean
(constructing the Cantor-Hausdorff measure on 2^ω, which does coincide with the Cantor-Lebesgue measure)
]

 -/

noncomputable def real_of_cantor : (ℕ → Bool) → ℝ :=
  λ x ↦ tsum (λ n : ℕ ↦ ite (x n = true) ((1:ℝ) / (2 ^ n.succ)) 0)

noncomputable def CantorLebesgueMeasureSubtype : MeasureTheory.Measure (
    {x : ℕ → Bool // ¬ ∃ k, x k = false ∧ ∀ l, k < l → x l = true}
) :=
  MeasureTheory.Measure.comap (λ x ↦ real_of_cantor x.1) MeasureTheory.volume

noncomputable def CantorLebesgueMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.map (λ x ↦ x.1) CantorLebesgueMeasureSubtype

-- using .map thanks to Kevin Buzzard suggestion
