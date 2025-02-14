import Mathlib.Data.Real.Hyperreal

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
  · refine Filter.mem_hyperfilter_of_finite_compl ?h.left.hf
    constructor
    · conv =>
        rhs
        change Fin 1
      symm
      use (by intro;exact ⟨0, by
        intro (hc : 0 < 0)
        omega
      ⟩)
      · exact fun _ => 0
      · exact fun z => Eq.symm (Fin.fin_one_eq_zero z)
      · intro (z : {x : ℕ // ¬ 0 < x})
        apply SetCoe.ext
        simp
        have := z.2
        omega
  · exact fun _ => id
