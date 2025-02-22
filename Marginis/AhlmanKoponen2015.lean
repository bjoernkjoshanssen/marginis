

import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
/-!

# Limit Laws and Automorphism Groups of Nonrigid Structures

[Ove Ahlman and Vera Koponen](http://logicandanalysis.org/index.php/jla/article/view/213)

The first sentence of the introduction reads as follows.

"[...] it has been shown that for any finite relational vocabulary (also called signature),
the proportion of labelled n-element structures which are rigid, ie have no nontrivial automorphism,
approaches 1 as n approaches infinity"

While their paper is about nonrigid structures, here we show that there exists a rigid 2-element structure, namely `Fin 2`
under addition.

-/
def automorphism_of_fin_2 (f : Fin 2 → Fin 2) :=
  Function.Bijective f ∧
  ∀ x y, f x + f y = f (x + y)

lemma fin2 (x : Fin 2) : x = 0 ∨ x = 1 := by
    fin_cases x <;> tauto

/-- `Fin 2` is rigid as an additive structure. -/
lemma fin2_rigid (f : Fin 2 → Fin 2) (hf : automorphism_of_fin_2 f) : f = id := by
  apply funext
  intro x
  simp
  have xalt: x = 0 ∨ x = 1 := fin2 _
  have fxalt: f x = 0 ∨ f x = 1 := fin2 _
  cases xalt with
  |inl hl =>
    let Q₀₀ := hf.2 0 0
    simp at Q₀₀
    subst hl
    exact Q₀₀
  |inr hr =>
    let Q₀₁ := hf.2 0 1
    subst hr
    let finj := hf.1.1
    by_contra c
    have assump: f 1 = 0 := by tauto
    simp at Q₀₁
    have: f 0 = f 1 := by
      apply Eq.trans
      exact Q₀₁
      exact assump.symm
    have := finj this
    exact Fin.zero_ne_one this

-- we can use this definition to talk about all labeled n-element sets for which we want the rigidity property.
  def automorphism_of_fin_k (k: ℕ)
  (f : Fin k → Fin k) :=
  Function.Bijective f ∧
  ∀ x y, f x + f y = f (x + y)

--a definition for calling Fin k rigid
  def is_rigid (k : ℕ) :=
  ∀ g, (automorphism_of_fin_k k g) → (g = id)
