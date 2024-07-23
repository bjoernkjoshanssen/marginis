import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-
The paper
Generating the Pfaffian closure with total Pfaffian functions
by GARETH JONES and PATRICK SPEISSEGGER
concerns Pfaffian functions for which
`df/dx = P(x,f(x))`
for a definable function P.
Here we demonstrate formally that if `f` is the exponential function,
then we can take `P` to be the projection on the second coordinate, `Prod.snd`
which should be definable in pretty much all settings and has a name in Lean
which does not require any `import`.

`Q` is a curried version of `P`.
-/

def P : ℝ × ℝ → ℝ := Prod.snd

noncomputable def f : ℝ → ℝ := Real.exp


example (x:ℝ) : deriv f x = P (x, (f x)) := by
  unfold P f
  rw [Real.deriv_exp]

def Q : ℝ → ℝ → ℝ := λ _ y ↦ y

example (x:ℝ) : deriv f x = Q x (f x) := by
  unfold Q f
  rw [Real.deriv_exp]
