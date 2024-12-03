import Mathlib.Data.Real.Hyperreal
/-!

## Elementary numerosity and measures
by VIERI BENCI
EMANUELE BOTTAZZI
MAURO DI NASSO

We construct a cardinality map from the powerset of any Fintype to the hyperreals.
-/

/-- Cardinality of a finite set, as a hyperreal. -/
def size {B : Type} [Fintype B] : Finset B → Hyperreal := by
  intro S
  let c := S.card
  apply Hyperreal.ofReal
  exact (c : ℝ)

/-- The cardinality of the empty set, as a hyperreal. -/
lemma size_empty {B : Type} [Fintype B] : size (B := B) ∅ = 0 := by
  unfold size
  simp only [Finset.card_empty, CharP.cast_eq_zero, Hyperreal.coe_zero]

/-- The cardinality of Bool, as a hyperreal. -/
lemma size_univ : size (Finset.univ : Finset Bool) = 2 := by
  unfold size
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, Nat.cast_ofNat,
    Hyperreal.coe_ofNat]

/-- The cardinality of a singleton, as a hyperreal. -/
lemma size_single {B : Type} [Fintype B] (b : B) : size {b} = 1 := by
  unfold size
  simp only [Finset.card_singleton, Nat.cast_one, Hyperreal.coe_one]
