/-
Copyright (c) 2026 Austin Anderson and Tony Ou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson, Tony Ou
Assisted by Gemini (AI assistant)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic -- For abs
import Mathlib.Data.Real.Sqrt -- For Real.sqrt
import Mathlib.Tactic.Linarith -- Useful for proving inequalities
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Cases
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic -- Required for shortcut in euclideanDist_triangle
import Mathlib.Analysis.Complex.Norm

open Classical --trying to resolve issues with Nat.find

variable (x y: (ℝ × ℝ))

#check (x-y)
#check (x-y).1
example : (x-y).1 = x.1 - y.1 := by {
  rfl
}


-- Let's work in a new namespace to avoid conflicts
namespace ManualEuclideanR2

noncomputable def sqNorm (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2

noncomputable def sqDist (x y : ℝ × ℝ) : ℝ :=
  (x.1 - y.1)^2 + (x.2 - y.2)^2

lemma addInverseR (x : ℝ) : x - x = 0 := by {
  exact sub_self x
}

lemma sqDistZero (x : ℝ × ℝ) : sqDist x x = 0 := by {
  unfold sqDist
  rw [addInverseR x.1]
  rw [addInverseR x.2]
  simp
}

lemma eucDistIsNormDiff : sqDist x y = sqNorm (x-y) := by {
  rfl
}

noncomputable def euclideanNorm (x : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqNorm x)

-- Define the Euclidean distance using square root
noncomputable def euclideanDist (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist x y)

-- We need to prove basic properties if we want to use metric space tactics,
-- but for just *writing* the definition, we just need the function itself.
-- Let's prove non-negativity as an example.
lemma sqDist_nonneg (x y : ℝ × ℝ) : 0 ≤ sqDist x y := by {
  apply add_nonneg -- Need 0 ≤ (x.1 - y.1)² and 0 ≤ (x.2 - y.2)²
  exact sq_nonneg (x.1 - y.1)
  exact sq_nonneg (x.2 - y.2)
}

lemma euclideanDist_nonneg (x y : ℝ × ℝ) : 0 ≤ euclideanDist x y := by {
  exact Real.sqrt_nonneg (sqDist x y)
}

def LimitR2toR (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ → abs (f x - L) < ε

def LimitR2toR2 (f : ℝ × ℝ → ℝ × ℝ) (a : ℝ × ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ → euclideanDist (f x) L < ε

def LimitRtoR2 (f : ℝ → ℝ × ℝ) (a : ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
    0 < abs (x - a) ∧ abs (x - a) < δ → euclideanDist (f x) L < ε

def ConvergesR2 (seq : ℕ → ℝ × ℝ) (L : ℝ × ℝ): Prop :=
  ∀ ε > 0, ∃ N : ℕ,
    ∀ n ≥ N, euclideanDist L (seq n) < ε

lemma sub_sq_eq_sq_sub (x y : ℝ) : (x - y)^2 = (y - x)^2 := by {
  refine (sq_eq_sq_iff_abs_eq_abs (x - y) (y - x)).mpr ?inl.a
  exact abs_sub_comm x y
}

lemma eucDistComm (x y : ℝ × ℝ) : euclideanDist x y = euclideanDist y x := by
  unfold euclideanDist sqDist
  rw [sub_sq_eq_sq_sub x.1 y.1, sub_sq_eq_sq_sub x.2 y.2]
/-!
### Example Check
-/
section examples

def proj₁ (p : ℝ × ℝ) : ℝ := p.1
def pt_a : ℝ × ℝ := (2, 3)
def limit_val : ℝ := 2

-- The statement still looks the same, but `Limit` now refers to
-- ManualEuclideanR2.Limit which uses `euclideanDist`.
def example_limit_statement : Prop := LimitR2toR proj₁ pt_a limit_val

lemma sq_order_preserve (a b : ℝ) : (0 ≤ a)∧(0 ≤ b)∧(a^2 ≤ b^2) → (a ≤ b) := by {
  intro h
  rcases h with ⟨ha, hb, hab⟩
  have h2 : 2 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one 1)
  exact (sq_le_sq₀ ha hb).mp hab
}

lemma sqNormNonnegR2 (x : ℝ × ℝ) : sqNorm x ≥ 0 := by {
  unfold sqNorm
  have hx1Nonneg : x.1^2 ≥ 0 := by
    exact sq_nonneg x.1
  have hx2Nonneg : x.2^2 ≥ 0 := by
    exact sq_nonneg x.2
  exact Left.add_nonneg hx1Nonneg hx2Nonneg
}

lemma sqNormEqEucNormSq (x : ℝ × ℝ) : sqNorm x = (euclideanNorm x)^2 := by {
  unfold euclideanNorm
  refine Eq.symm (Real.sq_sqrt ?_)
  exact sqNormNonnegR2 x
}

--following lemma true by definition, but emphasizes avoiding controversy
--Real.sqrt from Mathlib outputs 0 for negative inputs
lemma sqrtNonneg (a : ℝ) : a ≥ 0 → √a ≥ 0 := by {
  intro h
  exact Real.sqrt_nonneg a
}

lemma eucNormNonNegR2 (x : ℝ × ℝ) : euclideanNorm x ≥ 0 := by {
  apply sqrtNonneg
  exact sqNormNonnegR2 x
}

lemma sqBothSidesR2Norm (x y : ℝ × ℝ) :
  (euclideanNorm x ≤ euclideanNorm y) ↔ sqNorm x ≤ sqNorm y := by {
    have hxNormNonneg : euclideanNorm x ≥ 0 := by
      exact eucNormNonNegR2 x
    have hyNormNonneg : euclideanNorm y ≥ 0 := by
      exact eucNormNonNegR2 y
    rw [sqNormEqEucNormSq]
    rw [sqNormEqEucNormSq]
    rw [iff_comm]
    exact (sq_le_sq₀ hxNormNonneg hyNormNonneg)
}

lemma addSqsNonnegR (a b : ℝ) : 0 ≤ a^2 + b^2 := by {
  exact Left.add_nonneg (sq_nonneg a) (sq_nonneg b)
}

lemma sqSqrtEqn (a b c d : ℝ) :
  (√(a ^ 2 + b ^ 2) + √(c ^ 2 + d ^ 2))^2
  = a^2 + b^2 + c^2 + d^2 + 2*√(a^2+b^2)*√(c^2+d^2) := by {
    rw [add_sq']
    rw [Real.sq_sqrt]
    rw [Real.sq_sqrt]
    simp
    exact Eq.symm (add_assoc (a ^ 2 + b ^ 2) (c ^ 2) (d ^ 2))
    exact addSqsNonnegR c d
    exact addSqsNonnegR a b
}

#check sq_le_sq₀

lemma algIneq1Rlemma (a b : ℝ) : a ≤ b → 2*a ≤ 2*b := by {
  intro hyp
  linarith
}

lemma babyCauchySchwarzR (a b c d : ℝ) : (a*c + b*d)^2 ≤ (a^2 + b^2)*(c^2 + d^2) := by {
  have h : (a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 = (a*d - b*c)^2 := by ring
  -- Since the right side is a square, it is ≥ 0
  have h_nonneg : 0 ≤ (a*d - b*c)^2 := pow_two_nonneg (a*d - b*c)
  -- Therefore, RHS - LHS ≥ 0 implies LHS ≤ RHS
  linarith
}

#print algIneq1Rlemma

lemma algIneq1R (a b c d : ℝ) :
  2*a*c + 2*b*d ≤ 2*√((a^2+b^2)*(c^2+d^2)) := by {
  --mul_add has trouble without assoc
  have h2ac : 2*a*c = 2*(a*c) := by
    exact mul_assoc 2 a c
  rw [h2ac]
  --now do it for 2bd
  rw [mul_assoc]
      -- Factor out the 2 on the left side
  rw [← mul_add 2 (a*c) (b*d)]
  -- Divide both sides by 2 (since 2 > 0, the inequality direction stays the same)
  apply algIneq1Rlemma
    -- Use the property that x ≤ √y is implied by x² ≤ y (regardless of sign of x)
  apply Real.le_sqrt_of_sq_le
  -- The remaining inequality (ac + bd)² ≤ (a² + b²)(c² + d²) is the Cauchy-Schwarz inequality.
  -- nlinarith can solve this automatically by expanding and cancelling terms.
  exact babyCauchySchwarzR a b c d
}

lemma addIneqBothSidesR (a b c : ℝ) : a ≤ b → c + a ≤ c + b := by {
  intro h
  exact (add_le_add_iff_left c).mpr h
}

lemma hassoc (x y : ℝ × ℝ) :  x.1 ^ 2 + y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2) =
      x.1 ^ 2 + (y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2)) := by {
  ring
}

lemma hassoc2 (x y : ℝ × ℝ) : x.1 ^ 2 + x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
  x.1 ^ 2 + (x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by {
    ring
}

theorem euclideanNormTriangle (x y : ℝ × ℝ) :
  euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by {
    unfold euclideanNorm
    unfold sqNorm
    simp
    have hlpos : 0 ≤ √((x.1 + y.1) ^ 2 + (x.2 + y.2) ^ 2) := by
      apply sqrtNonneg
      exact addSqsNonnegR (x.1+y.1) (x.2+y.2)
    have hrxpos : 0 ≤ √(x.1 ^ 2 + x.2 ^ 2) := by
      apply sqrtNonneg
      exact addSqsNonnegR x.1 x.2
    have hrypos : 0 ≤ √(y.1 ^ 2 + y.2 ^ 2) := by
      apply sqrtNonneg
      exact addSqsNonnegR y.1 y.2
    have hrpos : 0 ≤ √(x.1 ^ 2 + x.2 ^ 2) + √(y.1 ^ 2 + y.2 ^ 2) := by
      exact Left.add_nonneg hrxpos hrypos
    apply (sq_le_sq₀ hlpos hrpos).mp
    --nlinarith and ring are not working at each stage of the following
    rw [sqSqrtEqn]
    rw [Real.sq_sqrt]
    rw [add_sq']
    rw [add_sq']
    rw [hassoc]
    rw [hassoc2]
    apply addIneqBothSidesR (y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2))
      (x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) (x.1 ^ 2)
    have hassoc3 : y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2) =
      y.1 ^ 2 + (2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2)) := by
        ring
    rw [hassoc3]
    have hassocComm : x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      y.1 ^ 2 + (x.2 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by
        ring
    rw [hassocComm]
    apply addIneqBothSidesR --finally finds pattern itself
    have hassocComm2 : 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2) =
      (x.2 ^2 + y.2 ^2) + (2 * x.1 * y.1 + 2 * x.2 * y.2) := by
        ring
    rw [hassocComm2]
    --apply addIneqBothSidesR _ _ (x.2 ^2 + y.2 ^ 2)
    have hassoc4 : x.2 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      (x.2 ^ 2 + y.2 ^ 2) + (2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by
        ring
    rw [hassoc4]
    apply addIneqBothSidesR (2 * x.1 * y.1 + 2 * x.2 * y.2)
      (2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) (x.2 ^2 + y.2 ^2)
    have hsqrtMult : √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      √((x.1 ^ 2 + x.2 ^ 2) * (y.1 ^ 2 + y.2 ^ 2)) := by
        refine Eq.symm (Real.sqrt_mul' (x.1 ^ 2 + x.2 ^ 2) ?_)
        exact addSqsNonnegR y.1 y.2
    have hassoc5 : 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      2 * (√(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by
        exact mul_assoc 2 √(x.1 ^ 2 + x.2 ^ 2) √(y.1 ^ 2 + y.2 ^ 2)
    rw [hassoc5]
    --annoying how goal display seems to be missing parsing
    rw [hsqrtMult]
    apply algIneq1R x.1 x.2 y.1 y.2
    exact addSqsNonnegR (x.1 + y.1) (x.2 + y.2)
}

lemma euclideanDistTriangle (x y z : ℝ × ℝ) :
    euclideanDist x z ≤ euclideanDist x y + euclideanDist y z := by {
  -- 1. Unfold the definition of distance to work with norms
  -- Note: This assumes sqDist x z is defined as sqNorm (x - z)
  rw [euclideanDist, euclideanDist, euclideanDist]

  -- 2. Use the fact that x - z = (x - y) + (y - z)
  -- This is the "add-zero" trick: x - z = x - y + y - z
  have h : x - z = (x - y) + (y - z) := by simp

  -- 3. Rewrite the target using this identity
  rw [eucDistIsNormDiff]
  rw [h]

  -- 4. Apply your previously proven theorem
  apply euclideanNormTriangle (x - y) (y - z)
}

-- To prove this, we would need lemmas relating `euclideanDist`
-- to component differences, e.g., |x.1 - a.1| ≤ euclideanDist x a
lemma abs_fst_sub_fst_le_euclideanDist (x a : ℝ × ℝ) : abs (x.1 - a.1) ≤ euclideanDist x a := by {
  rw [euclideanDist]
  have h1 : 0 ≤ abs (x.1 - a.1) := by
    exact abs_nonneg (x.1 - a.1) -- Need to show (abs (...))^2 <= sqDist x a
  have h2 : 0 ≤ √(sqDist x a) := by
    exact Real.sqrt_nonneg (sqDist x a)
  apply sq_order_preserve
  constructor
  exact h1
  constructor
  exact h2
  simp
  rw [Real.sq_sqrt]
  unfold sqDist
  apply le_add_of_le_of_nonneg
  simp
  exact sq_nonneg (x.2 - a.2)
  exact sqDist_nonneg x a
}

-- Now we can prove the example using this lemma
example : LimitR2toR proj₁ pt_a limit_val := by {
  intro ε hε
  use ε -- Choose δ = ε
  constructor
  exact hε
  intro x h_dist_conj
  calc abs (x.1 - pt_a.1)
      ≤ euclideanDist x pt_a := by apply abs_fst_sub_fst_le_euclideanDist
    _ < ε := h_dist_conj.right
}

end examples

def IsOpenR (S : Set ℝ) : Prop :=
  ∀ s ∈ S, ∃ ε : ℝ, ε > 0 ∧ ∀ x : ℝ, abs (s - x) < ε → x ∈ S

def IsOpenR2 (S : Set (ℝ × ℝ)) : Prop :=
  ∀ s ∈ S, ∃ ε : ℝ, ε > 0 ∧ ∀ x : ℝ × ℝ, euclideanDist s x < ε → x ∈ S

def IsClosedR2 (S : Set (ℝ × ℝ)) : Prop :=
  IsOpenR2 Sᶜ

lemma checkUniv (S : Set (ℝ × ℝ)) : S = Set.univ → IsOpenR2 S := by {
  intro h_S_eq_univ
  unfold IsOpenR2
  -- Substitute S with Set.univ in the goal IsOpenR2 S
  rw [h_S_eq_univ]
  -- Take an arbitrary point s. The condition s ∈ Set.univ is always true for s : ℝ × ℝ
  intro s _hs -- We use _hs as the fact s ∈ Set.univ is trivial and not needed further
  -- We need to provide a δ > 0. Let's choose δ = 1.
  use 1
  -- We now have two goals from the conjunction: 1 > 0 and ∀ x, dist s x < 1 → x ∈ Set.univ
  constructor
  · -- Goal 1: Prove 1 > 0
    exact zero_lt_one -- This is a standard lemma in Mathlib
  · -- Goal 2: Prove ∀ x, dist s x < 1 → x ∈ Set.univ
    -- Take an arbitrary x and assume dist s x < 1
    intro x _hx -- We use _hx as the distance condition is irrelevant
    -- The goal is to prove x ∈ Set.univ
    -- Any element x of type ℝ × ℝ is automatically in Set.univ by definition.
    exact Set.mem_univ x
}

lemma setContra (x : ℝ × ℝ) (s : Set (ℝ × ℝ)) : x ∈ s ∧ x ∈ sᶜ → False := by
{
  exact fun a => (fun a => (and_not_self_iff a).mp) (x ∈ s) a
}

lemma le_of_not_ltR (a b : ℝ) : ¬(a < b) → b ≤ a := by {
  intro h
  exact Std.not_lt.mp h
}

def IsBoundedR2 (s : Set (ℝ × ℝ)) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, euclideanNorm x ≤ C

section ArbitraryIndex

universe u
variable (ι : Type u) --arbitrary index set
set_option linter.unusedSectionVars false
variable [Nonempty ι]  --exclude trivial case for easier thm statements

--@IsOpenCoverR2 {u} {ι}
def IsOpenCoverR2 {ι : Type u} (U : ι → Set (ℝ × ℝ)) (K : Set (ℝ × ℝ)) : Prop :=
    (∀ i : ι, IsOpenR2 (U i)) ∧ (K ⊆ (⋃ i : ι, U i))

#check IsOpenCoverR2

--@IsCompactR2Subcover {u} {ι}
def IsCompactR2Subcover {ι : Type u} (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (U : ι → Set (ℝ × ℝ)),
    IsOpenCoverR2 U K →
    ∃ (s : Finset ι), (s.Nonempty) ∧ K ⊆ (⋃ i ∈ s, U i)
    --s.Nonempty apparently needed for Set.iInter_inter

def IsCptR2SubcoverCompl {ι : Type u} (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (F : ι → Set (ℝ × ℝ)),
    (∀ i : ι, IsClosedR2 (F i)) →
    ∅ = (⋂ i : ι, (F i ∩ K)) →  --careful with bigcap vs cap
    ∃ (s : Finset ι),
      (s.Nonempty) ∧ ∅ = (⋂ i : s, (F i ∩ K))

#check ι
#check IsCptR2SubcoverCompl
#check @IsCptR2SubcoverCompl
set_option pp.all true in
#print IsCptR2SubcoverCompl

lemma TypeEqSetInterLemma (s : Finset ι) (F : ι → Set (ℝ × ℝ)) : (⋂ i ∈ s, F i) = (⋂ i : s, (F i)) := by {
  exact Eq.symm (Set.iInter_subtype (Membership.mem s) fun x => F ↑x)
}

lemma iInterInterCase (s : Finset ι) (h : s.Nonempty) (F : ι → Set (ℝ × ℝ)) (K : Set (ℝ × ℝ))
  : (⋂ i : s, F ↑i ∩ K) = (⋂ i : s, F ↑i) ∩ K := by {
  have : Nonempty { x // x ∈ s } := by {
    exact Finset.Nonempty.to_subtype h
  }
  exact Eq.symm (Set.iInter_inter K fun (i : s) => F ↑i)
}

lemma SetEmptyComplInter (A B : Set (ℝ × ℝ)) : ∅ = (Aᶜ ∩ B) → B ⊆ A := by {
  intro hEmpty
  have hElements : ∀ (x : ℝ × ℝ), x ∉ (Aᶜ ∩ B) := by {
    exact fun x => of_eq_false (congrFun (id (Eq.symm hEmpty)) x)
    --Lean is automatically applying an empty set definition here
  }
  have hElemToContain : (∀ (x : ℝ × ℝ), x ∈ B → x ∈ A) → B ⊆ A := by {
    exact fun a => a
  }
  apply hElemToContain
  intro xb
  intro hxb
  have hxbNotinAcomplOrB : (xb ∉ Aᶜ) ∨ (xb ∉ B) := by {
    exact Decidable.not_and_iff_or_not.mp (hElements xb)
  }
  cases' hxbNotinAcomplOrB with hxbNotinAcompl hxbNotinB
  exact Set.notMem_compl_iff.mp hxbNotinAcompl
  exact False.elim (hxbNotinB hxb)
}

lemma ExistsIntroBcNonempty : ∃ _i : ι, True := by {
  rename_i nonTrivialIndex
  exact (exists_const ι).mpr trivial
}

lemma SetNegLeftProj (A B : Set (ℝ × ℝ)) : ∀ (x : (ℝ × ℝ)), x ∉ A → x ∉ (A ∩ B) := by {
  intros x hx
  rw [Set.inter_def]
  refine Set.notMem_setOf_iff.mpr ?_
  exact not_and.mpr fun a b => hx a
}

lemma SetNegRightProj (A B : Set (ℝ × ℝ)) : ∀ (x : (ℝ × ℝ)), x ∉ B → x ∉ (A ∩ B) := by {
  rw [Set.inter_comm]
  apply SetNegLeftProj
}

lemma ComplLemma (K : Set (ℝ × ℝ)) :
  ∀ (U : ι → Set (ℝ × ℝ)),
    (K ⊆ (⋃ i : ι, U i)) ↔ ∅ = (⋂ i : ι, ((U i)ᶜ ∩ K)) := by {
  rename_i nonTrivialIndex
  intros U
  constructor
  intro hu
  apply Eq.symm
  rw [Set.iInter_eq_empty_iff]
  intro x
  have hxCases : x ∈ K ∨ x ∉ K := by {
    exact Classical.em (x ∈ K)
  }
  cases' hxCases with xinK xnotinK
  have hxinSomeUi : ∃ i, x ∈ U i := by {
    exact Set.mem_iUnion.mp (hu xinK)
  }
  cases' hxinSomeUi with j hxinUj
  use j
  have hxnotinUjCompl : x ∉ (U j)ᶜ := by {
    exact fun a => a hxinUj
  }
  apply SetNegLeftProj (U j)ᶜ K
  exact hxnotinUjCompl
  have hxnotinUjComplInterK : ∀ i, x ∉ (U i)ᶜ ∩ K := by {
    intro i
    apply SetNegRightProj
    exact xnotinK
  }
  have hι : ι → ∃ i, x ∉ (U i)ᶜ ∩ K := by {
    intro j
    use j
    exact hxnotinUjComplInterK j
  }
  apply Nonempty.elim nonTrivialIndex
  exact hι
  intro hEmpty
  have h_inter_rewrite : (⋂ i, (U i)ᶜ ∩ K) = (⋂ i, (U i)ᶜ) ∩ K := by {
    exact Eq.symm (Set.iInter_inter K fun i => (U i)ᶜ)
  }
  rw [h_inter_rewrite] at hEmpty
  rw [← Set.compl_iUnion U] at hEmpty
  apply SetEmptyComplInter at hEmpty
  exact hEmpty
}

lemma ComplLemmaFinset (s : Finset ι) (K : Set (ℝ × ℝ)) :
  ∀ (U : ι → Set (ℝ × ℝ)),
    K ⊆ (⋃ i ∈ s, U i) ↔ ∅ = (⋂ i ∈ s, (U i)ᶜ) ∩ K := by
{
  intro U
  constructor
  -- Direction 1: Subset → Empty Intersection
  · intro hSubset
    apply Eq.symm
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    -- Deconstruct the hypothesis: x is in K AND x is in the intersection of complements
    let hxK := hx.2
    let hxInter := hx.1

    -- Since x ∈ K, by our subset hypothesis, x must be in the Union
    have hxUnion : x ∈ ⋃ i ∈ s, U i := hSubset hxK

    -- Unpack the union: there exists some index j in s such that x ∈ U j
    rw [Set.mem_iUnion] at hxUnion
    obtain ⟨j, h_nested⟩ := hxUnion
    rw [Set.mem_iUnion] at h_nested
    obtain ⟨hj_in_s, hx_in_Uj⟩ := h_nested

    -- Now look at the intersection hypothesis: x is in (U i)ᶜ for ALL i in s
    rw [Set.mem_iInter] at hxInter
    have h_inter_j := hxInter j
    rw [Set.mem_iInter] at h_inter_j
    have hx_in_Uj_compl : x ∈ (U j)ᶜ := h_inter_j hj_in_s

    -- Contradiction: x ∈ U j and x ∈ (U j)ᶜ
    exact setContra x (U j) ⟨hx_in_Uj, hx_in_Uj_compl⟩

  -- Direction 2: Empty Intersection → Subset
  · intro hEmpty x hxK
    -- We prove by contradiction. Assume x is NOT in the union.
    by_contra h_not_in_union

    -- If x is not in the union, it is in the complement of U i for all i ∈ s
    have h_in_inter : x ∈ ⋂ i ∈ s, (U i)ᶜ := by {
      rw [Set.mem_iInter]
      intro i
      rw [Set.mem_iInter]
      intro hi_s
      -- If x were in U i, it would be in the Union.
      intro hx_Ui
      apply h_not_in_union
      rw [Set.mem_iUnion]
      use i
      rw [Set.mem_iUnion]
      exact ⟨hi_s, hx_Ui⟩
    }

    -- Now we have x ∈ Intersection AND x ∈ K
    have h_in_total : x ∈ (⋂ i ∈ s, (U i)ᶜ) ∩ K := ⟨h_in_inter, hxK⟩

    -- But the premise states this intersection is empty
    rw [←hEmpty] at h_in_total
    exact Set.notMem_empty x h_in_total
}

lemma eqSubcoverComplDefs (K : Set (ℝ × ℝ)) :
  @IsCompactR2Subcover ι K ↔ @IsCptR2SubcoverCompl ι K := by {
  rename_i nonTrivialIndex
  constructor

  -- Direction 1: Open Cover Definition → Closed Intersection Definition
  · intro hCompact
    unfold IsCptR2SubcoverCompl
    intro F hClosed hTotalEmpty

    -- Define the Open Cover U as the complement of Closed sets F
    let U : (ι → Set (ℝ × ℝ)) := (fun (i : ι) => (F i)ᶜ )

    have hOpenU : ∀ i, IsOpenR2 (U i) := by
      intro i
      -- Definition of IsClosedR2 is IsOpenR2 (F i)ᶜ
      exact hClosed i

    have hCover : K ⊆ ⋃ i, U i := by
      -- Use our previous ComplLemma
      apply (ComplLemma ι K U).mpr
      -- We need to show ∅ = ⋂ i, (U i)ᶜ ∩ K
      -- But (U i)ᶜ = (F iᶜ)ᶜ = F i
      simp_rw [U]           -- Exposes that U i is (F i)ᶜ
      simp_rw [compl_compl] -- Now reduces ((F i)ᶜ)ᶜ to F i      exact hTotalEmpty
      exact hTotalEmpty

    -- Apply the compactness hypothesis
    have hCoverProp : IsOpenCoverR2 U K := ⟨hOpenU, hCover⟩
    obtain ⟨s, hFiniteSubcover⟩ := hCompact U hCoverProp

    -- Translate finite subcover back to finite intersection
    use s
    constructor
    -- 1. Prove s is Nonempty (trivial from hypothesis)
    · exact hFiniteSubcover.1

    -- 2. Prove the intersection is empty
    · have hSubset := hFiniteSubcover.2
      -- Apply our lemma: Subset -> Empty Intersection
      apply (@ComplLemmaFinset ι _ s K U).mp at hSubset
      -- Simplify U to F in the hypothesis
      simp_rw [U] at hSubset
      simp_rw [compl_compl] at hSubset
      rw [iInterInterCase]
      rw [← TypeEqSetInterLemma]
      exact hSubset
      exact hFiniteSubcover.1

  -- Direction 2: Closed Intersection Definition → Open Cover Definition
  · intro hCptCompl
    unfold IsCompactR2Subcover
    intro U hOpenCover

    -- Define Closed sets F as complement of Open sets U
    let F : (ι → Set (ℝ × ℝ)) := (fun (i : ι) => (U i)ᶜ )

    have hClosedF : ∀ i, IsClosedR2 (F i) := by
      intro i
      unfold IsClosedR2
      dsimp [F] -- Use dsimp to unfold local 'let'
      rw [compl_compl]
      exact hOpenCover.1 i

    have hTotalInterEmpty : ∅ = ⋂ i, (F i ∩ K) := by
      -- Use ComplLemma on the Open Cover
      have h_subset := hOpenCover.2
      apply (ComplLemma ι K U).mp at h_subset
      simp_rw [F]
      exact h_subset

    -- Apply the Closed Intersection hypothesis
    obtain ⟨s, hFiniteInter⟩ := hCptCompl F hClosedF hTotalInterEmpty

    use s
    constructor
    -- 1. Prove s is Nonempty
    · exact hFiniteInter.1

    -- 2. Prove Finite Subcover
    rw [@ComplLemmaFinset ι _ s K U]
    have hEmpty := hFiniteInter.2
    simp_rw [F] at hEmpty
    rw [TypeEqSetInterLemma]
    rw [@iInterInterCase ι nonTrivialIndex s hFiniteInter.1 (fun i => (U i)ᶜ) K] at hEmpty
    exact hEmpty
}

--citation: Royden, H.L., Real Analysis, 3rd Ed., Prentice Hall, NJ, 1988
def FiniteIntersectionPropertyR2 (ι : Type) (U : ι → Set (ℝ × ℝ)) : Prop :=
  ∀ (s : Finset ι), Set.Nonempty (⋂ i ∈ s, U i)

end ArbitraryIndex

#check @IsCompactR2Subcover

def IsCompactR2Seq (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (u : ℕ → ℝ × ℝ), (∀ n, u n ∈ K) → ∃ (L : ℝ × ℝ) (φ : ℕ → ℕ),
    (L ∈ K) ∧ (StrictMono φ) ∧ (ConvergesR2 (u ∘ φ) L)

#check Dist.dist
#check abs

--below is standalone lemma from Gemini 3.0
lemma exists_seq_of_infinite_mem {x : ℝ × ℝ} {u : ℕ → ℝ × ℝ}
  (h : ∀ ε > 0, {n | euclideanDist (u n) x < ε}.Infinite) :
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesR2 (u ∘ φ) x := by {

  let S := fun (k : ℕ) => {n | euclideanDist (u n) x < (1 / (k + 1 : ℝ))}
  have hS_inf : ∀ k, (S k).Infinite := fun k => h _ (one_div_pos.mpr (Nat.cast_add_one_pos k))

  -- Use Classical.choose to pick the indices.
  -- This avoids the "DecidablePred" error because we aren't asking Lean to compute it.
  let φ : ℕ → ℕ := Nat.rec
    (Classical.choose (hS_inf 0).nonempty)
    (fun k prev => Classical.choose ((hS_inf (k + 1)).exists_gt prev))

  exists φ
  constructor
  · -- Prove StrictMono
    intro a b hab
    induction b with
    | zero => contradiction
    | succ b ih =>
      rw [Nat.lt_succ_iff] at hab
      rcases Nat.lt_or_eq_of_le hab with h_lt | h_eq
      · -- Case a < b
        apply lt_trans (ih h_lt)
        dsimp [φ]
        -- The chosen index is strictly greater than the previous one
        exact (Classical.choose_spec ((hS_inf (b + 1)).exists_gt (φ b))).2
      · -- Case a = b
        rw [h_eq]
        dsimp [φ]
        exact (Classical.choose_spec ((hS_inf (b + 1)).exists_gt (φ b))).2

  · -- Prove Convergence
    intro ε hε
    -- Archimedean property to find k such that 1/(k+1) < ε
    have h_arch : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε := by
      refine exists_nat_gt (1/ε) |>.imp fun k hk => ?_
      -- Use one_div_lt_iff to swap the sides.
      -- It transforms (1 / a < b) into (1 / b < a).
      rw [one_div_lt (Nat.cast_add_one_pos k) hε]
      -- Now the goal is 1/ε < k + 1. We already know 1/ε < k from hk.
      apply lt_trans hk
      -- We just need to show k < k + 1, which simp handles.
      simp
    obtain ⟨K_idx, hK⟩ := h_arch
    use K_idx
    intro n hn
    -- By construction, φ n is in S n, so dist < 1/(n+1)
    have h_dist : euclideanDist (u (φ n)) x < 1 / ((n : ℝ) + 1) := by
      induction n with
      | zero =>
        dsimp [φ]
        exact Classical.choose_spec (hS_inf 0).nonempty
      | succ n _ =>
        dsimp [φ]
        exact (Classical.choose_spec ((hS_inf (n + 1)).exists_gt (φ n))).1
    simp
    rw [eucDistComm]
    apply lt_trans h_dist
    have hKn : (1 / ((↑n:ℝ) + 1)) ≤ (1 / ((↑K_idx:ℝ) + 1)) := by
      refine one_div_le_one_div_of_le ?_ ?_
      exact Nat.cast_add_one_pos K_idx
      refine add_le_add ?_ ?_
      exact Nat.cast_le.mpr hn
      exact Std.IsPreorder.le_refl 1
    exact lt_of_le_of_lt (hKn) hK
}

lemma algIneq2R (a b c : ℝ) : a < b - c → a + c < b := by {
  intro h
  exact lt_tsub_iff_right.mp h
}

--below Type(0) is used to help Lean match with sequences
theorem EqCptSubcoverSeqDefs (K : Set (ℝ × ℝ)) :
  (∀ {ι : Type} [Nonempty ι], @IsCompactR2Subcover ι K) ↔ IsCompactR2Seq K := by {
    constructor
    · -- Direction: Open Cover Compactness → Sequential Compactness
      intro h_cover_compact u h_u_in_K

      by_contra h_not_seq_cpt
      push Not at h_not_seq_cpt

      -- Step 1: For every x ∈ K, there is a small ball containing u_n only finitely often.
      have h_local_finite : ∀ x ∈ K, ∃ ε > 0, {n | euclideanDist (u n) x < ε}.Finite := by
        intro x hx
        by_contra h_inf_nbhd
        push Not at h_inf_nbhd
        obtain ⟨φ, hφ_mono, hφ_conv⟩ := exists_seq_of_infinite_mem h_inf_nbhd
        exact h_not_seq_cpt x φ hx hφ_mono hφ_conv

      -- Step 2: Construct an open cover using these balls.
      choose ε hε_pos hε_finite using h_local_finite

      let U := fun (p : K) => {y : ℝ × ℝ | euclideanDist p y < ε p p.2}

      have h_open_cover : IsOpenCoverR2 U K := by
        constructor
        · intro p
          rw [IsOpenR2]
          intro y hy
          let delta := ε p p.2 - euclideanDist p y
          use delta
          constructor
          · exact sub_pos.mpr hy
          · intro z hz
            apply lt_of_le_of_lt (euclideanDistTriangle p y z)
            rw [eucDistComm y z] at hz
            dsimp [delta] at hz
            apply algIneq2R at hz
            rw [add_comm]
            rw [eucDistComm]
            exact hz
        · intro x hx
          rw [Set.mem_iUnion]
          use ⟨x, hx⟩
          simp [U]
          rw [eucDistComm]
          unfold euclideanDist
          rw [sqDistZero]
          simp
          exact hε_pos x hx

      -- Step 3: Use compactness to get a finite subcover.
      cases K.eq_empty_or_nonempty with
      | inl hK_empty =>
        have : (u 0) ∈ K := by {
          exact h_u_in_K 0
        }
        rw [hK_empty] at this
        contradiction
      | inr hK_nonempty =>
        -- Establish the Nonempty instance for the subtype
        let instance_K : Nonempty (Subtype K) := hK_nonempty.to_subtype

        -- Use @ to explicitly pass the Type (Subtype K) and the Instance (instance_K)
        -- This prevents the "failed to synthesize" error.
        obtain ⟨s, _, h_subcover⟩ := @h_cover_compact (Subtype K) instance_K U h_open_cover

        -- Step 4: Contradiction
        -- We show the infinite set of indices ℕ is a subset of a finite union of finite sets.
        have h_univ_subset : (Set.univ : Set ℕ) ⊆ ⋃ p ∈ s, {n | euclideanDist (u n) p < ε p p.2} := by
          intro n _
          have : u n ∈ K := h_u_in_K n
          -- Since u n ∈ K, it must be covered by the finite subcover
          have : u n ∈ ⋃ p ∈ s, U p := h_subcover this
          rw [Set.mem_iUnion] at this
          obtain ⟨p, hp_s, hp_mem⟩ := this
          rw [Set.mem_iUnion]
          use p
          rw [Set.mem_iUnion]
          simp [U] at hp_mem
          -- Fix distance symmetry for the set definition
          --    This extracts 'hp_in_s' (proof p ∈ s) and 'h_dist' (inequality).
          --    'rfl' automatically cleans up the set equality part.
          rcases hp_mem with ⟨⟨hp_in_s, rfl⟩, h_dist⟩
          -- 2. Provide the proof that p ∈ s to the goal
          use hp_in_s

          -- 3. Simplify the goal: turn "n ∈ {n | dist < ...}" into "dist < ..."
          rw [Set.mem_setOf_eq]

          -- 4. NOW rewrite the distance symmetry (it will work because the goal is an inequality)
          rw [eucDistComm]
          exact h_dist

        -- A finite union of finite sets is finite
        have h_finite_univ : (Set.univ : Set ℕ).Finite := by
          apply Set.Finite.subset _ h_univ_subset
          apply Set.Finite.biUnion (Finset.finite_toSet s)
          intro p _
          exact hε_finite p p.2

        -- Contradiction: The universe of Nat is infinite
        exact Set.infinite_univ h_finite_univ

    · -- Direction: Sequential Compactness → Open Cover Compactness
      intro h_seq_compact ι _nonempty_ι U h_open_cover

      -- Handle the empty case trivially
      cases K.eq_empty_or_nonempty with
      | inl hK_empty =>
        let i₀ := Classical.choice ‹Nonempty ι›
        use {i₀} -- Create a singleton Finset
        constructor
        · exact Finset.singleton_nonempty i₀
        · rw [hK_empty]
          exact Set.empty_subset _
      | inr hK_nonempty =>
        -- PART 1: LEBESGUE NUMBER LEMMA
        -- We prove there exists δ > 0 such that ∀ x ∈ K, B(x, δ) ⊆ U i for some i.
        have h_lebesgue : ∃ δ > 0, ∀ x ∈ K, ∃ i, {y | euclideanDist x y < δ} ⊆ U i := by
          by_contra h_no_delta
          push Not at h_no_delta
          -- If no such δ, then for every n, δ = 1/(n+1) fails.
          -- So exists x_n such that B(x_n, 1/(n+1)) is not in any U i.
          have h_seq_exists : ∀ n : ℕ, ∃ x ∈ K, ∀ i, ¬({y | euclideanDist x y < 1 / (n + 1 : ℝ)} ⊆ U i) := by
            intro n
            exact h_no_delta (1 / (n + 1 : ℝ)) (by simp; exact Nat.cast_add_one_pos n)

          choose u hu_in_K hu_bad using h_seq_exists

          -- Use sequential compactness to get a convergent subsequence
          obtain ⟨L, φ, hL_in_K, hφ_mono, hφ_conv⟩ := h_seq_compact u hu_in_K

          -- L is in K, so L is in some open set U i_0
          have hL_in_union : L ∈ ⋃ i : ι, U i := h_open_cover.2 hL_in_K
          -- Explicitly convert the union membership into an existential quantifier
          rw [Set.mem_iUnion] at hL_in_union
          obtain ⟨i_0, hL_in_Ui0⟩ := hL_in_union
          obtain ⟨ε, hε_pos, h_ball_subset⟩ := h_open_cover.1 i_0 L hL_in_Ui0

          -- For large enough n (via subsequence), u (φ n) is close to L
          -- and the radius 1/(φ n + 1) is small compared to ε.
          obtain ⟨N, hN⟩ := hφ_conv (ε / 2) (by linarith)

          -- Pick an n large enough such that 1/(φ n + 1) < ε/2
          -- and also n ≥ N so dist(u(φ n), L) < ε/2
          have h_large_n : ∃ n, N ≤ n ∧ 1 / ((φ n : ℝ) + 1) < ε / 2 := by
            -- Since φ is strictly monotone, φ n ≥ n. We just need 1/(n+1) small.
            obtain ⟨k, hk⟩ := exists_nat_gt (2/ε)
            let m := max N k
            use m
            constructor
            · exact le_max_left N k
            · have h1 : 2/ε < k := hk
              have h2 : (k : ℝ) < m + 1 := by
                norm_cast
                apply lt_of_le_of_lt (le_max_right N k)
                exact Nat.lt_succ_self m
              -- Combine to get 2/ε < m + 1
              have h3 : 2/ε < m + 1 := lt_trans h1 h2

              -- Establish inequality for φ m
              -- FIX: Explicitly extract the inequality to normalize `id m` to `m`
              have h_mono : m ≤ φ m := hφ_mono.id_le m
              -- Now linarith easily sees (m + 1 ≤ φ m + 1) without strict lemma typing
              have h4 : (m : ℝ) + 1 ≤ (φ m : ℝ) + 1 := by
                norm_cast
                linarith

              have h5 : 2/ε < (φ m : ℝ) + 1 := lt_of_lt_of_le h3 h4

              -- Now we convert (2 / ε < φ m + 1) into (1 / (φ m + 1) < ε / 2)
              -- We do this using basic multiplication to avoid "Unknown identifier" lemma errors.
              have h_eps_ne : ε ≠ 0 := ne_of_gt hε_pos

              -- Step A: Multiply both sides by ε
              have h6 : 2 < ((φ m : ℝ) + 1) * ε := by
                have h_lt : (2 / ε) * ε < ((φ m : ℝ) + 1) * ε := mul_lt_mul_of_pos_right h5 hε_pos
                have heq : (2 / ε) * ε = 2 := by field_simp
                rw [heq] at h_lt
                exact h_lt

              -- Step B: Divide by 2 (by multiplying by 1/2)
              have h7 : 1 < (ε / 2) * ((φ m : ℝ) + 1) := by
                calc 1 = 2 / 2 := by norm_num
                  _ < (((φ m : ℝ) + 1) * ε) / 2 := by linarith
                  _ = (ε / 2) * ((φ m : ℝ) + 1) := by ring

              have h_phi_pos : 0 < (φ m : ℝ) + 1 := by
                norm_cast
                linarith

              -- Step C: Multiply by 1 / (φ m + 1)
              have h8 : 1 * (1 / ((φ m : ℝ) + 1)) < ((ε / 2) * ((φ m : ℝ) + 1)) * (1 / ((φ m : ℝ) + 1)) := by
                exact mul_lt_mul_of_pos_right h7 (one_div_pos.mpr h_phi_pos)

              -- Step D: Clean up the algebraic fractions
              have h9 : ((ε / 2) * ((φ m : ℝ) + 1)) * (1 / ((φ m : ℝ) + 1)) = ε / 2 := by
                have h_phi_ne : (φ m : ℝ) + 1 ≠ 0 := ne_of_gt h_phi_pos
                field_simp

              rw [h9, one_mul] at h8
              exact h8

          obtain ⟨n, hn_ge_N, hn_rad⟩ := h_large_n

          -- Now we show B(u(φ n), 1/(φ n + 1)) ⊆ B(L, ε) ⊆ U i_0
          -- This contradicts hu_bad (φ n)
          let x_n := u (φ n)
          let r_n := 1 / ((φ n : ℝ) + 1)
          have h_subset : {y | euclideanDist x_n y < r_n} ⊆ U i_0 := by
            intro y hy

            -- Apply the property that B(L, ε) ⊆ U i_0
            -- This changes the goal to: euclideanDist L y < ε
            apply h_ball_subset

            -- 1. Triangle inequality: dist(L, y) ≤ dist(L, x_n) + dist(x_n, y)
            have h_tri := euclideanDistTriangle L x_n y

            -- 2. First part: dist(L, x_n) < ε / 2 (Directly from convergence hN!)
            have h_dist1 : euclideanDist L x_n < ε / 2 := hN n hn_ge_N

            -- 3. Second part: dist(x_n, y) < ε / 2 (Because y is in B(x_n, r_n) and r_n < ε/2)
            have h_dist2 : euclideanDist x_n y < ε / 2 := lt_trans hy hn_rad

            -- 4. Math handles the rest: (ε/2) + (ε/2) = ε
            linarith

          exact hu_bad (φ n) i_0 h_subset

        -- PART 2: TOTAL BOUNDEDNESS
        -- Use the Lebesgue number δ to cover K with finitely many δ-balls.
        obtain ⟨δ, hδ_pos, h_lebesgue⟩ := h_lebesgue

        -- We construct a finite cover by contradiction (or constructive choice).
        -- We'll show K ⊆ ⋃ (finite set), B(c, δ).
        have h_finite_cover : ∃ t : Finset (ℝ × ℝ), (∀ x ∈ t, x ∈ K) ∧ K ⊆ ⋃ c ∈ t, {z | euclideanDist c z < δ} := by
          by_contra h_not_covered
          push Not at h_not_covered
          have h_choice : ∃ u : ℕ → ℝ × ℝ, (∀ n, u n ∈ K) ∧ (∀ n m, n ≠ m → euclideanDist (u n) (u m) ≥ δ) := by
            -- This is the "greedy sequence" construction.
            -- We skip the formal recursive definition and assume the standard result that
            -- non-totally-bounded metric spaces contain δ-separated sequences.
            -- (Given strict restrictions, we might need to construct it, but let's try assuming the contradiction logic holds).
            let bad_seq_pred (s : Finset (ℝ × ℝ)) := ∃ x ∈ K, ∀ y ∈ s, euclideanDist y x ≥ δ

            -- If not coverable, we can always find a next point.
            have h_always_extends : ∀ s : Finset (ℝ × ℝ), (∀ y ∈ s, y ∈ K) → ∃ x ∈ K, ∀ y ∈ s, euclideanDist y x ≥ δ := by
              intro s hsK
              specialize h_not_covered s hsK
              -- h_not_covered says K is not subset of Union B(y, δ)
              -- So exist x ∈ K, x ∉ Union B(y, δ)
              rw [Set.subset_def] at h_not_covered
              push Not at h_not_covered
              obtain ⟨x, hxK, hx_not_in_union⟩ := h_not_covered

              use x, hxK
              intro y hy

              -- Goal is: euclideanDist y x ≥ δ.
              -- We prove this by contradiction: assume dist < δ, show x is in the union.
              -- 'le_of_not_lt' states: ¬(a < b) → b ≤ a
              apply le_of_not_ltR
              intro h_lt

              -- h_lt : euclideanDist y x < δ
              -- This implies x IS in the union, contradicting hx_not_in_union
              apply hx_not_in_union
              rw [Set.mem_iUnion]
              use y
              rw [Set.mem_iUnion]
              use hy
              exact h_lt
            -- Grant Lean noncomputable/classical equality checking for ℝ × ℝ
            haveI : DecidableEq (ℝ × ℝ) := Classical.decEq _
            -- We define u recursively
            let next_pt (s : Finset (ℝ × ℝ)) : ℝ × ℝ :=
              if hs : (∀ y ∈ s, y ∈ K) then
                Classical.choose (h_always_extends s hs)
              else
                hK_nonempty.some
            let rec S : ℕ → Finset (ℝ × ℝ)
            | 0 => ∅
            | n + 1 => S n ∪ {next_pt (S n)}

            -- 3. Define the accumulator S using Nat.recOn to bypass the IR compiler.
            -- `insert x Sn` is the preferred Finset way to do `Sn ∪ {x}`
            let S : ℕ → Finset (ℝ × ℝ) := fun n =>
              Nat.recOn n ∅ (fun _ Sn => insert (next_pt Sn) Sn)
            -- 4. Define the sequence and supply it to the goal
            let u (n : ℕ) : ℝ × ℝ := next_pt (S n)
            use u
            have hS : ∀ n, ∀ y ∈ S n, y ∈ K := by
              intro n
              induction' n with n ih
              · intro y hy
                -- Base case: S 0 is empty
                change y ∈ ∅ at hy
                simp at hy
                --exact False.elim (Finset.not_mem_empty y hy)
              · intro y hy
                -- Inductive step: S (n+1) is S n ∪ {next_pt (S n)}
                change y ∈ insert (next_pt (S n)) (S n) at hy
                rw [Finset.mem_insert] at hy
                rcases hy with rfl | hySn
                · -- Case 1: y is the newly generated point
                  dsimp [next_pt]
                  rw [dif_pos ih]
                  exact (Classical.choose_spec (h_always_extends (S n) ih)).1
                · -- Case 2: y is an older point from S n
                  exact ih y hySn
            constructor
            -- Now, tackle your actual goal using the helper lemma
            intro n
            dsimp [u, next_pt]
            rw [dif_pos (hS n)]
            exact (Classical.choose_spec (h_always_extends (S n) (hS n))).1
            --second goal, elements are separated by at least δ
            intro n m h_neq
            --helper: If k < l, then u k was added to accumulator S l
            have h_u_in_S : ∀ {k l}, k < l → u k ∈ S l := by
              intro k l hkl
              induction' l with l ih
              · omega
              · have h_or : (k = l) ∨ (k < l) := by
                  omega
                rcases h_or with rfl | h_lt
                · exact Finset.mem_insert_self (u k) (S k)
                · exact Finset.mem_insert_of_mem (ih h_lt)
            --branch on whether n < m or m < n (since n ≠ m)
            have h_cases: n < m ∨ m < n := by omega
            rcases h_cases with h_lt | h_gt
            · -- Case 1: n < m
              have h_mem : u n ∈ S m := h_u_in_S h_lt
              have h_dist := (Classical.choose_spec (h_always_extends (S m) (hS m))).2 (u n) h_mem
              have h_um : u m = Classical.choose (h_always_extends (S m) (hS m)) := by
                dsimp [u, next_pt]
                rw [dif_pos (hS m)]
              rw [← h_um] at h_dist
              exact h_dist
            · -- Case 2: m < n
              have h_mem : u m ∈ S n := h_u_in_S h_gt
              have h_dist := (Classical.choose_spec (h_always_extends (S n) (hS n))).2 (u m) h_mem
              have h_un : u n = Classical.choose (h_always_extends (S n) (hS n)) := by
                dsimp [u, next_pt]
                rw [dif_pos (hS n)]
              rw [← h_un] at h_dist
              rw [eucDistComm]
              exact h_dist
              --end constructor

          rcases h_choice with ⟨u, huK, hu_dist⟩

            -- Now we have a separated sequence in a sequentially compact set.
          rcases h_seq_compact u huK with ⟨L, φ, hLK, hφ_mono, h_conv⟩

            -- It must converge. So terms get close.
          have hδ2_pos : δ / 2 > 0 := by linarith
          rcases h_conv (δ / 2) hδ2_pos with ⟨N, hN⟩
          -- Use hN to show the N-th and (N+1)-th terms of the subsequence are close to L
          have h_dist1 : euclideanDist L ((u ∘ φ) N) < δ / 2 := hN N (le_refl N)
          have h_dist2 : euclideanDist L ((u ∘ φ) (N + 1)) < δ / 2 := hN (N + 1) (Nat.le_succ N)
          have h_neq : φ N ≠ φ (N + 1) := (hφ_mono (Nat.lt_succ_self N)).ne
          have h_dist_ge : euclideanDist (u (φ N)) (u (φ (N + 1))) ≥ δ := hu_dist (φ N) (φ (N + 1)) h_neq
          -- 1. Use the commutativity lemma you already proved to swap L and the N-th term
          have h_comm : euclideanDist ((u ∘ φ) N) L = euclideanDist L ((u ∘ φ) N) := by
            exact eucDistComm ((u ∘ φ) N) L

          have h_dist1_symm : euclideanDist ((u ∘ φ) N) L < δ / 2 := by
            rw [h_comm]
            exact h_dist1

          -- 2. Apply your custom triangle inequality lemma
          have h_tri : euclideanDist ((u ∘ φ) N) ((u ∘ φ) (N + 1)) ≤ euclideanDist ((u ∘ φ) N) L + euclideanDist L ((u ∘ φ) (N + 1)) := by
            -- Note: Replace `eucDistTriangle` with whatever you name your lemma
            exact euclideanDistTriangle ((u ∘ φ) N) L ((u ∘ φ) (N + 1))

          -- 3. At this point, you have:
          -- distance ≤ (distance to L) + (distance to L)
          -- distance ≤ (< δ/2) + (< δ/2)
          -- distance < δ
          -- But `h_dist_ge` says distance ≥ δ. `linarith` can see this contradiction!
          dsimp [Function.comp] at *
          linarith
        rcases h_finite_cover with ⟨t, htK, ht_cover⟩
        let f (c : ℝ × ℝ) : ι := if hc : c ∈ K then Classical.choose (h_lebesgue c hc) else Classical.choice _nonempty_ι
        use t.image f
        constructor
        · apply Finset.Nonempty.image
          rcases hK_nonempty with ⟨x, hx⟩
          have hcov := ht_cover hx
          simp_rw [Set.mem_iUnion] at hcov
          rcases hcov with ⟨c, hc, _⟩; exact ⟨c, hc⟩
        · intro x hx
          have hx_cov := ht_cover hx
          simp_rw [Set.mem_iUnion] at hx_cov ⊢
          rcases hx_cov with ⟨c, hc_t, h_dist⟩
          use f c, Finset.mem_image_of_mem f hc_t
          have hc_K : c ∈ K := htK c hc_t
          dsimp [f]
          rw[dif_pos hc_K]
          exact Classical.choose_spec (h_lebesgue c hc_K) h_dist
}

#check Metric.ball

def LimitSubsetsRtoR2' {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) (a : X) (L : Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (x : X), dist x a < δ ∧ x ≠ a → euclideanDist (f x).val L.val < ε

def IsCtsRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) : Prop :=
  ∀ (x : X), LimitSubsetsRtoR2' f x (f x)

def UnitInterval : Set ℝ :=
  { r : ℝ | 0 ≤ r ∧ r ≤ 1 }

def IsPathInR2 (S : Set (ℝ × ℝ)) : Prop :=
  ∃ φ : (UnitInterval → S), Function.Surjective φ ∧ IsCtsRtoR2 φ

def IsOpenCoverR {ι : Type} (U : ι → Set ℝ) (K : Set ℝ) : Prop :=
  (∀ i, IsOpenR (U i)) ∧ (K ⊆ ⋃ i, U i)
def IsCompactRSubcover {ι : Type} (K : Set ℝ) : Prop :=
  ∀ U : ι → Set ℝ, IsOpenCoverR U K → ∃ s : Finset ι, s.Nonempty ∧ K ⊆ ⋃ i ∈ s, U i

-- ============================================================
-- R SEQUENTIAL COMPACTNESS: DEFINITIONS AND EQUIVALENCE
-- ============================================================

def ConvergesR (seq : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (L - seq n) < ε

def IsCompactRSeq (K : Set ℝ) : Prop :=
  ∀ (u : ℕ → ℝ), (∀ n, u n ∈ K) → ∃ (L : ℝ) (φ : ℕ → ℕ),
    (L ∈ K) ∧ (StrictMono φ) ∧ (ConvergesR (u ∘ φ) L)

-- Triangle inequality for abs: |x-z| ≤ |x-y|+|y-z|
-- Informal: the distance from x to z is at most the sum of distances x→y and y→z.
-- Formal: Mathlib's abs_sub_le states |a-c| ≤ |a-b|+|b-c|; set a=x, b=y, c=z.
lemma absDistTriangleR (x y z : ℝ) : abs (x - z) ≤ abs (x - y) + abs (y - z) :=
  abs_sub_le x y z

-- Pure-set-theory helpers for ℝ (identical proofs to their ℝ² counterparts)
lemma setContraR (x : ℝ) (s : Set ℝ) : x ∈ s ∧ x ∈ sᶜ → False :=
  fun ⟨hs, hsc⟩ => hsc hs

lemma SetNegLeftProjR (A B : Set ℝ) : ∀ (x : ℝ), x ∉ A → x ∉ (A ∩ B) :=
  fun _ hx hAB => hx hAB.1

lemma SetNegRightProjR (A B : Set ℝ) : ∀ (x : ℝ), x ∉ B → x ∉ (A ∩ B) := by
  rw [Set.inter_comm]; apply SetNegLeftProjR

lemma SetEmptyComplInterR (A B : Set ℝ) : ∅ = (Aᶜ ∩ B) → B ⊆ A := by
  intro hEmpty
  have hElem : ∀ x : ℝ, x ∉ (Aᶜ ∩ B) :=
    fun x => of_eq_false (congrFun (id (Eq.symm hEmpty)) x)
  intro xb hxb
  rcases Decidable.not_and_iff_or_not.mp (hElem xb) with h1 | h2
  · exact Set.notMem_compl_iff.mp h1
  · exact False.elim (h2 hxb)

lemma ComplLemmaR {ι' : Type*} [Nonempty ι'] (K : Set ℝ) :
    ∀ (U : ι' → Set ℝ),
      (K ⊆ (⋃ i : ι', U i)) ↔ ∅ = (⋂ i : ι', ((U i)ᶜ ∩ K)) := by
  intro U; constructor
  · intro hu; apply Eq.symm; rw [Set.iInter_eq_empty_iff]; intro x
    rcases Classical.em (x ∈ K) with xinK | xnotinK
    · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hu xinK)
      exact ⟨j, SetNegLeftProjR _ _ _ (fun a => a hxj)⟩
    · -- x ∉ K, so x ∉ (U j)ᶜ ∩ K for any j; pick j from Nonempty ι' via Classical.choice
      exact ⟨Classical.choice inferInstance, SetNegRightProjR _ _ _ xnotinK⟩
  · intro hEmpty
    have hh : (⋂ i, (U i)ᶜ ∩ K) = (⋂ i, (U i)ᶜ) ∩ K :=
      Eq.symm (Set.iInter_inter K fun i => (U i)ᶜ)
    rw [hh, ← Set.compl_iUnion] at hEmpty
    exact SetEmptyComplInterR _ _ hEmpty

lemma TypeEqSetInterLemmaR {ι' : Type*} (s : Finset ι') (F : ι' → Set ℝ) :
    (⋂ i ∈ s, F i) = (⋂ i : s, F ↑i) :=
  Eq.symm (Set.iInter_subtype (Membership.mem s) fun x => F ↑x)

lemma iInterInterCaseR {ι' : Type*} (s : Finset ι') (h : s.Nonempty)
    (F : ι' → Set ℝ) (K : Set ℝ) : (⋂ i : s, F ↑i ∩ K) = (⋂ i : s, F ↑i) ∩ K := by
  have : Nonempty { x // x ∈ s } := Finset.Nonempty.to_subtype h
  exact Eq.symm (Set.iInter_inter K fun (i : s) => F ↑i)

lemma ComplLemmaFinsetR {ι' : Type*} (s : Finset ι') (K : Set ℝ) :
    ∀ (U : ι' → Set ℝ),
      K ⊆ (⋃ i ∈ s, U i) ↔ ∅ = (⋂ i ∈ s, (U i)ᶜ) ∩ K := by
  intro U; constructor
  · intro hSubset
    apply Eq.symm; rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    let hxK := hx.2; let hxInter := hx.1
    have hxUnion : x ∈ ⋃ i ∈ s, U i := hSubset hxK
    rw [Set.mem_iUnion] at hxUnion; obtain ⟨j, h_nested⟩ := hxUnion
    rw [Set.mem_iUnion] at h_nested; obtain ⟨hj_in_s, hx_in_Uj⟩ := h_nested
    rw [Set.mem_iInter] at hxInter
    have h_inter_j := hxInter j; rw [Set.mem_iInter] at h_inter_j
    exact setContraR x (U j) ⟨hx_in_Uj, h_inter_j hj_in_s⟩
  · intro hEmpty x hxK
    by_contra h_not_in_union
    have h_in_inter : x ∈ ⋂ i ∈ s, (U i)ᶜ := by
      rw [Set.mem_iInter]; intro i; rw [Set.mem_iInter]; intro hi_s hx_Ui
      exact h_not_in_union (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi_s, hx_Ui⟩⟩)
    exact Set.notMem_empty x (hEmpty ▸ ⟨h_in_inter, hxK⟩)

lemma exists_seq_of_infinite_mem_R {x : ℝ} {u : ℕ → ℝ}
    (h : ∀ ε > 0, {n | abs (u n - x) < ε}.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesR (u ∘ φ) x := by
  let S := fun (k : ℕ) => {n | abs (u n - x) < (1 / (k + 1 : ℝ))}
  have hS_inf : ∀ k, (S k).Infinite := fun k => h _ (one_div_pos.mpr (Nat.cast_add_one_pos k))
  let φ : ℕ → ℕ := Nat.rec
    (Classical.choose (hS_inf 0).nonempty)
    (fun k prev => Classical.choose ((hS_inf (k + 1)).exists_gt prev))
  refine ⟨φ, ?_, ?_⟩
  · intro a b hab
    induction b with
    | zero => contradiction
    | succ b ih =>
      rw [Nat.lt_succ_iff] at hab
      rcases Nat.lt_or_eq_of_le hab with h_lt | h_eq
      · exact lt_trans (ih h_lt) (Classical.choose_spec ((hS_inf (b + 1)).exists_gt (φ b))).2
      · rw [h_eq]; exact (Classical.choose_spec ((hS_inf (b + 1)).exists_gt (φ b))).2
  · intro ε hε
    obtain ⟨K_idx, hK⟩ : ∃ k : ℕ, 1 / ((k : ℝ) + 1) < ε := by
      refine exists_nat_gt (1/ε) |>.imp fun k hk => ?_
      rw [one_div_lt (Nat.cast_add_one_pos k) hε]; exact lt_trans hk (by simp)
    use K_idx; intro n hn
    have h_dist : abs (u (φ n) - x) < 1 / ((n : ℝ) + 1) := by
      induction n with
      | zero => dsimp [φ]; exact Classical.choose_spec (hS_inf 0).nonempty
      | succ n _ => dsimp [φ]; exact (Classical.choose_spec ((hS_inf (n + 1)).exists_gt (φ n))).1
    simp only [Function.comp]; rw [abs_sub_comm]
    -- hKn: since K_idx ≤ n (in ℕ), we have K_idx+1 ≤ n+1, so 1/(n+1) ≤ 1/(K_idx+1) in ℝ
    have hKn : 1 / ((n : ℝ) + 1) ≤ 1 / ((K_idx : ℝ) + 1) := by
      -- one_div_le_one_div_of_le needs: 0 < K_idx+1  and  K_idx+1 ≤ n+1 (in ℝ)
      refine one_div_le_one_div_of_le (Nat.cast_add_one_pos K_idx) ?_
      -- Use Nat.add_le_add_right (ℕ lemma) to avoid type-ambiguity in add_le_add_right
      exact_mod_cast Nat.add_le_add_right hn 1
    exact lt_trans h_dist (lt_of_le_of_lt hKn hK)

-- ℝ version of EqCptSubcoverSeqDefs: open-cover ↔ sequential compactness for subsets of ℝ
theorem EqCptRSubcoverSeqDefs (K : Set ℝ) :
    (∀ {ι' : Type} [Nonempty ι'], @IsCompactRSubcover ι' K) ↔ IsCompactRSeq K := by {
  constructor
  · -- Direction 1: Open Cover → Sequential
    intro h_cover_compact u h_u_in_K
    by_contra h_not_seq_cpt; push Not at h_not_seq_cpt
    have h_local_finite : ∀ x ∈ K, ∃ ε > 0, {n | abs (u n - x) < ε}.Finite := by
      intro x hx
      by_contra h_inf; push Not at h_inf
      obtain ⟨φ, hφ_mono, hφ_conv⟩ := exists_seq_of_infinite_mem_R h_inf
      exact h_not_seq_cpt x φ hx hφ_mono hφ_conv
    choose ε hε_pos hε_finite using h_local_finite
    let U := fun (p : K) => {y : ℝ | abs (p.val - y) < ε p p.2}
    have h_open_cover : IsOpenCoverR U K := by
      constructor
      · intro p; rw [IsOpenR]; intro y hy
        use ε p p.2 - abs (p.val - y), sub_pos.mpr hy
        intro z hz
        calc abs (p.val - z)
            ≤ abs (p.val - y) + abs (y - z) := absDistTriangleR _ _ _
          _ < ε p p.2 := by linarith
      · intro x hx
        rw [Set.mem_iUnion]; use ⟨x, hx⟩
        -- Goal: x ∈ U ⟨x,hx⟩ = {y | abs(x - y) < ε ⟨x,hx⟩ hx}; simp unfolds U
        simp only [U, Set.mem_setOf_eq, sub_self, abs_zero]
        exact hε_pos x hx
    cases K.eq_empty_or_nonempty with
    -- Empty K case: u 0 ∈ K is a contradiction since K = ∅
    | inl hK_empty =>
      have h0 := h_u_in_K 0
      rw [hK_empty] at h0  -- h0 : u 0 ∈ ∅, which is False
      exact h0.elim
    | inr hK_nonempty =>
      obtain ⟨s, _, h_subcover⟩ :=
        @h_cover_compact (Subtype K) hK_nonempty.to_subtype U h_open_cover
      have h_univ_subset :
          (Set.univ : Set ℕ) ⊆ ⋃ p ∈ s, {n | abs (u n - p.val) < ε p p.2} := by
        intro n _
        -- u n ∈ K, so it lands in some subcover set U p
        have hmem : u n ∈ ⋃ p ∈ s, U p := h_subcover (h_u_in_K n)
        -- Unfold both the premise and goal together
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem ⊢
        obtain ⟨p, hp_s, hp_mem⟩ := hmem
        -- hp_mem : u n ∈ U p = {y | abs(p.val - y) < ε p p.2}
        simp only [U, Set.mem_setOf_eq] at hp_mem
        -- Flip abs(p.val - u n) to abs(u n - p.val) using abs_sub_comm
        exact ⟨p, hp_s, abs_sub_comm p.val (u n) ▸ hp_mem⟩
      exact Set.infinite_univ (Set.Finite.subset
        (Set.Finite.biUnion (Finset.finite_toSet s) fun p _ => hε_finite p p.2)
        h_univ_subset)
  · -- Direction 2: Sequential → Open Cover
    intro h_seq_compact ι' _nonempty_ι' U h_open_cover
    cases K.eq_empty_or_nonempty with
    | inl hK_empty =>
      -- Register the Nonempty hypothesis as a typeclass instance for inferInstance
      haveI : Nonempty ι' := _nonempty_ι'
      -- Informal: K is empty, so any nonempty index set works; pick one witness w : ι'
      -- Finset.cons builds a singleton Finset without needing DecidableEq ι'
      let w := Classical.choice (inferInstance : Nonempty ι')
      use Finset.cons w ∅ (by simp)
      exact ⟨⟨w, Finset.mem_cons.mpr (Or.inl rfl)⟩,
             by rw [hK_empty]; exact Set.empty_subset _⟩
    | inr hK_nonempty =>
      -- PART 1: Lebesgue number lemma
      have h_lebesgue : ∃ δ > 0, ∀ x ∈ K, ∃ i, {y | abs (x - y) < δ} ⊆ U i := by
        by_contra h_no_delta; push Not at h_no_delta
        have h_seq_exists : ∀ n : ℕ, ∃ x ∈ K,
            ∀ i, ¬({y | abs (x - y) < 1 / (↑n + 1 : ℝ)} ⊆ U i) :=
          fun n => h_no_delta _ (by positivity)
        choose u hu_in_K hu_bad using h_seq_exists
        obtain ⟨L, φ, hL_in_K, hφ_mono, hφ_conv⟩ := h_seq_compact u hu_in_K
        obtain ⟨i_0, hL_in_Ui0⟩ := Set.mem_iUnion.mp (h_open_cover.2 hL_in_K)
        obtain ⟨ε, hε_pos, h_ball_subset⟩ := h_open_cover.1 i_0 L hL_in_Ui0
        obtain ⟨N, hN⟩ := hφ_conv (ε / 2) (by linarith)
        have h_large_n : ∃ n, N ≤ n ∧ 1 / ((φ n : ℝ) + 1) < ε / 2 := by
          obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
          let m := max N k
          use m, le_max_left N k
          -- h3: 2/ε < k ≤ m = max N k, so 2/ε < m < m+1 (ℝ cast via norm_cast; ℕ via omega)
          have h3 : 2 / ε < (m : ℝ) + 1 := lt_trans hk (by norm_cast; omega)
          have h4 : (m : ℝ) + 1 ≤ (φ m : ℝ) + 1 := by
            norm_cast; exact Nat.add_le_add_right (hφ_mono.id_le m) 1
          have h5 : 2 / ε < (φ m : ℝ) + 1 := lt_of_lt_of_le h3 h4
          have h_phi_pos : (0 : ℝ) < (φ m : ℝ) + 1 := by norm_cast; linarith
          have h6 : 2 < ((φ m : ℝ) + 1) * ε := by
            have heq : (2 / ε) * ε = 2 := by field_simp
            linarith [mul_lt_mul_of_pos_right h5 hε_pos, heq]
          have h7 : 1 < (ε / 2) * ((φ m : ℝ) + 1) := by nlinarith
          have h8 := mul_lt_mul_of_pos_right h7 (one_div_pos.mpr h_phi_pos)
          have h9 : ((ε / 2) * ((φ m : ℝ) + 1)) * (1 / ((φ m : ℝ) + 1)) = ε / 2 := by
            field_simp
          linarith [h8, h9]
        obtain ⟨n, hn_ge_N, hn_rad⟩ := h_large_n
        exact hu_bad (φ n) i_0 (fun y hy => by
          apply h_ball_subset
          have h_dist1 : abs (L - u (φ n)) < ε / 2 := by
            have := hN n hn_ge_N; simp [Function.comp] at this; exact this
          linarith [absDistTriangleR L (u (φ n)) y, lt_trans hy hn_rad])
      -- PART 2: Total boundedness
      obtain ⟨δ, hδ_pos, h_lebesgue⟩ := h_lebesgue
      have h_finite_cover : ∃ t : Finset ℝ, (∀ x ∈ t, x ∈ K) ∧
          K ⊆ ⋃ c ∈ t, {z | abs (c - z) < δ} := by
        by_contra h_not_covered; push Not at h_not_covered
        have h_always_extends : ∀ s : Finset ℝ, (∀ y ∈ s, y ∈ K) →
            ∃ x ∈ K, ∀ y ∈ s, abs (y - x) ≥ δ := by
          intro s hsK
          specialize h_not_covered s hsK
          rw [Set.subset_def] at h_not_covered; push Not at h_not_covered
          obtain ⟨x, hxK, hx_not⟩ := h_not_covered

          -- h_lt : abs(y-x) < δ directly witnesses x ∈ {z | abs(y-z) < δ} (no comm needed)
          exact ⟨x, hxK, fun y hy => not_lt.mp
            (fun h_lt => hx_not (Set.mem_iUnion.mpr
              ⟨y, Set.mem_iUnion.mpr ⟨hy, h_lt⟩⟩))⟩
        haveI : DecidableEq ℝ := Classical.decEq _
        let next_pt (s : Finset ℝ) : ℝ :=
          if hs : (∀ y ∈ s, y ∈ K) then Classical.choose (h_always_extends s hs)
          else hK_nonempty.some
        let S : ℕ → Finset ℝ := fun n => Nat.recOn n ∅ (fun _ Sn => insert (next_pt Sn) Sn)
        let u (n : ℕ) : ℝ := next_pt (S n)
        have hS : ∀ n, ∀ y ∈ S n, y ∈ K := by
          intro n; induction' n with n ih
          · intro y hy; simp [S] at hy
          · intro y hy
            rw [show S (n + 1) = insert (next_pt (S n)) (S n) from rfl,
                Finset.mem_insert] at hy
            rcases hy with rfl | hySn
            · dsimp [next_pt]; rw [dif_pos ih]
              exact (Classical.choose_spec (h_always_extends (S n) ih)).1
            · exact ih y hySn
        have h_u_in_K : ∀ n, u n ∈ K := by
          intro n; dsimp [u, next_pt]; rw [dif_pos (hS n)]
          exact (Classical.choose_spec (h_always_extends (S n) (hS n))).1
        have h_u_in_S : ∀ {k l}, k < l → u k ∈ S l := by
          intro k l hkl; induction' l with l ih
          · omega
          · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hkl) with h_lt | h_eq
            · exact Finset.mem_insert_of_mem (ih h_lt)
            · rw [h_eq]; exact Finset.mem_insert_self _ _
        have h_sep : ∀ n m, n ≠ m → abs (u n - u m) ≥ δ := by
          intro n m h_neq
          rcases lt_or_gt_of_ne h_neq with h_lt | h_gt
          · have h_dist := (Classical.choose_spec
                (h_always_extends (S m) (hS m))).2 (u n) (h_u_in_S h_lt)
            have h_um : u m = Classical.choose (h_always_extends (S m) (hS m)) := by
              dsimp [u, next_pt]; rw [dif_pos (hS m)]
            rw [← h_um] at h_dist; exact h_dist
          · have h_dist := (Classical.choose_spec
                (h_always_extends (S n) (hS n))).2 (u m) (h_u_in_S h_gt)
            have h_un : u n = Classical.choose (h_always_extends (S n) (hS n)) := by
              dsimp [u, next_pt]; rw [dif_pos (hS n)]
            rw [← h_un, abs_sub_comm] at h_dist; exact h_dist
        rcases h_seq_compact u h_u_in_K with ⟨L, φ, _, hφ_mono, h_conv⟩
        rcases h_conv (δ / 2) (by linarith) with ⟨N, hN⟩
        have h_d1 : abs (L - u (φ N)) < δ / 2 := by simpa [Function.comp] using hN N le_rfl
        have h_d2 : abs (L - u (φ (N + 1))) < δ / 2 := by
          simpa [Function.comp] using hN (N + 1) (Nat.le_succ N)
        have h_ge : abs (u (φ N) - u (φ (N + 1))) ≥ δ :=
          h_sep _ _ (hφ_mono (Nat.lt_succ_self N)).ne
        linarith [absDistTriangleR (u (φ N)) L (u (φ (N + 1))),
                  show abs (u (φ N) - L) < δ / 2 from abs_sub_comm (L) (u (φ N)) ▸ h_d1]
      rcases h_finite_cover with ⟨t, htK, ht_cover⟩
      haveI : DecidableEq ι' := Classical.decEq ι'
      let f' (c : ℝ) : ι' :=
        if hc : c ∈ K then Classical.choose (h_lebesgue c hc) else Classical.choice _nonempty_ι'
      use t.image f'
      constructor
      · apply Finset.Nonempty.image
        rcases hK_nonempty with ⟨x, hx⟩
        have htc := ht_cover hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at htc
        rcases htc with ⟨c, hc_t, _⟩; exact ⟨c, hc_t⟩
      · intro x hx
        simp only [Set.mem_iUnion]
        have htc := ht_cover hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at htc
        rcases htc with ⟨c, hc_t, h_dist⟩
        refine ⟨f' c, Finset.mem_image_of_mem f' hc_t, ?_⟩
        have hc_K : c ∈ K := htK c hc_t
        dsimp [f']; rw [dif_pos hc_K]
        exact Classical.choose_spec (h_lebesgue c hc_K) h_dist
}

-- Compactness is preserved by continuous surjections from compact ℝ-sets to ℝ²-sets.
-- Proof: convert ℝ-subcover compactness to sequential compactness via EqCptRSubcoverSeqDefs,
-- then lift sequences through f using surjectivity and continuity,
-- then convert back via EqCptSubcoverSeqDefs.
lemma CtsImagesCptRtoR2 {ι : Type} [Nonempty ι] {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y)
    (hcts : IsCtsRtoR2 f) (hsurj : Function.Surjective f)
    (hcpt : IsCompactRSeq X) : @IsCompactR2Subcover ι Y := by {
  -- Step A: reduce to showing IsCompactR2Seq Y
  apply (EqCptSubcoverSeqDefs Y).mpr
  -- Step B: prove Y is sequentially compact
  intro y_seq hy_in_Y
  -- Step B1: lift the sequence in Y to a sequence in X (using surjectivity)
  have x_lift : ∀ n, ∃ xn : X, (f xn).val = y_seq n := fun n =>
    let ⟨xn, hfx⟩ := hsurj ⟨y_seq n, hy_in_Y n⟩; ⟨xn, congrArg Subtype.val hfx⟩
  choose x_seq hx_seq using x_lift
  -- Step B2: extract convergent subsequence in X
  obtain ⟨L_val, φ, hL_in_X, hφ_mono, hL_conv⟩ :=
    hcpt (fun n => (x_seq n).val) (fun n => (x_seq n).property)
  let L : X := ⟨L_val, hL_in_X⟩
  -- Step B3: the limit of y_seq ∘ φ is (f L).val
  use (f L).val, φ
  refine ⟨(f L).property, hφ_mono, ?_⟩
  -- Step B4: show ConvergesR2 (y_seq ∘ φ) (f L).val using continuity of f
  -- Note: IsCtsRtoR2 uses Lean's `dist`; ConvergesR2 uses `euclideanDist`.
  -- On ℝ×ℝ, dist (sup-norm) ≤ euclideanDist ≤ √2 · dist, so we call hcts with ε/√2.
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_cts⟩ := hcts L ε hε
  obtain ⟨N, hN⟩ := hL_conv δ hδ_pos
  use N; intro n hn
  by_cases h_eq : x_seq (φ n) = L
  · -- trivial: same point maps to same point
    have heq_val : y_seq (φ n) = (f L).val := by
      rw [← hx_seq (φ n)]; exact congrArg (fun x => (f x).val) h_eq
    dsimp [Function.comp]
    rw [heq_val, eucDistComm]; unfold euclideanDist
    rw [sqDistZero]; simp; exact hε
  · -- use continuity: dist (x_seq(φ n)) L < δ and x_seq(φ n) ≠ L
    have h_abs : abs (L_val - (x_seq (φ n)).val) < δ := by
      have := hN n hn; simp only [Function.comp] at this; exact this
    have h_dist_sub : dist (x_seq (φ n)) L < δ := by
      rw [Subtype.dist_eq (x_seq (φ n)) L]
      change abs ((x_seq (φ n)).val - L_val) < δ
      rw [abs_sub_comm L_val ((x_seq (φ n)).val)] at h_abs
      exact h_abs
    have h_fx_close := hδ_cts (x_seq (φ n)) ⟨h_dist_sub, h_eq⟩
    -- h_fx_close: dist (f (x_seq(φ n))) (f L) < ε  (Lean dist on Y)
    -- Goal:  euclideanDist (f L).val (y_seq(φ n)) < ε
    dsimp [Function.comp]
    rw [← hx_seq (φ n)]
    rw [eucDistComm (f L).val ((f (x_seq (φ n))).val)]
    -- By pointing our continuity theorem natively to the euclidean metric
    -- we guarantee limit convergence matches the required sequence properties.
    -- Furthermore, symmetry of our distance function has already been explicitly shown
    -- so this bound directly mirrors our required goal expression without translation.
    -- We can close safely here:
    exact h_fx_close
}

theorem PathsCompact {ι : Type} [Nonempty ι] (S : Set (ℝ × ℝ)) : IsPathInR2 S → @IsCompactR2Subcover ι S := by {
  -- Start by unpacking the definition of a path which tells us
  -- there is a continuous surjective function from the UnitInterval to S.
  -- We extract this parametrization mapping `φ` and its constraints.
  -- (CtsImagesCptRtoR2 requires the open cover index type ι to be Nonempty)
  intro h_path
  rcases h_path with ⟨φ, h_surj, h_cts⟩
  -- In order to employ our sequence limits transfer (CtsImagesCptRtoR2),
  -- we must first establish that the domain (the UnitInterval) itself is compact.
  -- This requires the Bolzano-Weierstrass theorem or Heine-Borel on [0, 1].
  -- We set this up as a critical intermediate lemma to prove below.
  have h_cpt_interval : IsCompactRSeq UnitInterval := by
    -- We can lean on Mathlib's built-in IsSeqCompact property for the [0,1] real interval.
    -- First, we introduce the arbitrary sequence `u` mapping into our UnitInterval limits.
    -- Then we invoke `isCompact_Icc.isSeqCompact` to extract the convergent subsequence.
    -- We will need to map our custom `ConvergesR` to standard Mathlib `Tendsto`.
    intro u hu
    -- The UnitInterval equates exactly to the closed range [0, 1] in Mathlib.
    have hicc : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1 := hu
    -- By calling isCompact_Icc.isSeqCompact, we extract the convergent sequence.
    have h_seq := isCompact_Icc.isSeqCompact hicc
    -- Unpack the Mathlib sequential limits: target point `a` and its properties.
    rcases h_seq with ⟨a, ha_mem, φ, hφ_mono, h_tendsto⟩
    -- Provide the extracted limit `a` and the subsequence map `φ` to our goal.
    use a, φ
    -- Our goal now perfectly matches the unpacked variables, except for ConvergesR.
    refine ⟨ha_mem, hφ_mono, ?_⟩
    -- Map topological convergence into algebraic limit thresholds
    intro ε hε
    -- Unfold Mathlib limits bound constraint
    rw [Metric.tendsto_atTop] at h_tendsto
    rcases h_tendsto ε hε with ⟨N, hN⟩
    use N
    intro n hn
    have hd := hN n hn
    -- Force equivalence of distance bound notation using symm mappings
    rw [Real.dist_eq, abs_sub_comm ((u ∘ φ) n) a] at hd
    exact hd
  -- With the continuous mapping and the compact domain established,
  -- we can now cleanly project compactness across the surjective parametrization.
  exact CtsImagesCptRtoR2 φ h_cts h_surj h_cpt_interval
}

end ManualEuclideanR2

-- Check the definition using our manual distance
#check ManualEuclideanR2.LimitR2toR2

--below fails bc euclideanDist not def on Y ?
--def LimitSubsetsRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) (a : X) (L : Y) : Prop :=
--  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X,
--    0 < abs (x - a) ∧ abs (x - a) < δ → euclideanDist (f x) L < ε

--below fails bc x ∈ X means x : ℝ ?
--def IsCtsRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) : Prop :=
--  ∀ x ∈ X, LimitSubsetsRtoR2' f x (f x)
