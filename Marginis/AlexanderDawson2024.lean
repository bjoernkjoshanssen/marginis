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

open Int in
/-- A "chain rule". -/
theorem prim_com_eq_starr (x y : Int) :
  prim (com x y) = starr (com (prim x) y) (prim y) := by
  simp [prim, com, starr]
  apply (Int.add_right_inj 1).mp
  by_cases h₀ : x * y = 0
  · rw [h₀,sub_mul]
    ring_nf
    exact h₀.symm
  · rw [sub_add_cancel, Int.sub_mul]
    simp
