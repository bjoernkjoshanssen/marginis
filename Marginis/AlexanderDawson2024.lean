/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Homeomorph

/-!
# Hyperreal differentiation with an idempotent ultrafilter
Samuel Allen Alexander and Bryan Dawson

In light of the discussion on page 1 of differentiating numbers,
we choose a way to define this and prove the Chain Rule.
-/

/-- A "derivative". -/
def prim (n : Int) : Int := n - 1

/-- A "composition". -/
def com (x y : Int) : Int := x * y

/-- A "multiplication".  -/
def starr (x y : Int) : Int := x + y

/-- A "chain rule". -/
theorem prim_com_eq_starr : ∀ x y : Int,
  prim (com x y) = starr (com (prim x) y) (prim y) := by
  intros x y
  simp [prim, com, starr]
  suffices  x * y - 1 + 1 = (x - 1) * y + (y - 1) + 1 by
    exact (Int.add_right_inj 1).mp this
  have g₀ : (x - 1) * y = x * y - 1 * y := Int.sub_mul x 1 y
  by_cases h₀ : x * y = 0
  · rw [h₀]
    simp
    rw [g₀]
    ring_nf
    exact h₀.symm
  · have : x * y - 1 + 1 = x* y := Int.sub_add_cancel (x * y) 1
    rw [this, g₀]
    simp
