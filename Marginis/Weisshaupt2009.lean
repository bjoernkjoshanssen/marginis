import Mathlib.Data.Real.Hyperreal
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!

## Diffusion processes via parabolic equations: an infinitesimal approach to Lindeberg’s limit theorem
Heinz Weisshaupt

The paper discusses hyperreals. We show that the infinitesimal `fun n => 1/n` is greater than 0.

-/

lemma zero_lt_reciprocals: Hyperreal.ofSeq (fun _ => 0) < Hyperreal.ofSeq (fun n => 1/n) := by
  refine Hyperreal.ofSeq_lt_ofSeq.mpr ?_
  refine Filter.eventually_iff_exists_mem.mpr ?_
  use (fun x => 0 < x)
  simp
  constructor
  · apply Filter.mem_hyperfilter_of_finite_compl
    constructor
    · symm
      use (fun (_ : Fin 1) => ⟨0, by intro (hc : 0 < 0); omega⟩)
      · exact fun _ => 0
      · exact fun z => Eq.symm (Fin.fin_one_eq_zero z)
      · exact fun (z : {x : ℕ // ¬ 0 < x}) => SetCoe.ext <| by
          have := z.2
          simp only
          omega
  · exact fun _ => id


/-- An axiom that should be independent of other axioms. -/
example : ∀ x : Hyperreal, ∃ y, x = Hyperreal.ofSeq y :=
  fun x => Quotient.exists.mp ⟨x,rfl⟩
