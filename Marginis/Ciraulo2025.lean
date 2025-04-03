import Mathlib.Order.Basic
import Mathlib.Tactic

/-!

## Kuratowski’s problem in constructive Topology
FRANCESCO CIRAULO

We proved lemma 2.2 using the following formal theorems
`theorem_1` through `theorem_10`.

-/

variable {α : Type} [PartialOrder α]

variable (c : α → α) -- c is a function between α
axiom cl_1 : ∀ (x : α), x ≤ c x
axiom cl_2 : ∀ (x : α), c (c x) = c x
axiom cl_3 : ∀ {x y : α}, x ≤ y → c x ≤ c y
-- Define closure operation

variable (i : α → α) -- i is a function between α
axiom int_1 : ∀ (x : α), i x ≤ x
axiom int_2 : ∀ (x : α), i (i x) = i x
axiom int_3 : ∀ {x y : α}, x ≤ y → i x ≤ i y
-- Define interior operation

-- lemmas which do not depend on the space --
theorem lemma_1 : ∀ (x : α), i x ≤ i (c (i x)) := by -- i ≤ ici
  intro x
  have h1 := @cl_1 α _
  have h2 := @int_3 α _
  have h3 := int_2 i x
  nth_rewrite 1 [← h3]
  apply h2
  apply h1


theorem lemma_2 :  ∀ (x : α), i (c (i x)) ≤ i (c x):= by -- ici ≤ ic
  intro x
  have h1 := @cl_3 α
  have h2 := @int_3 α
  have h3 := @int_1 α
  apply h1
  apply h2
  apply h3

theorem lemma_3 : ∀ (x : α), i (c (i x)) ≤ c (i x):= by -- ici ≤ ci
  intro x
  have h1 := @int_1 α
  apply h1

theorem lemma_4 : ∀ (x : α), i (c x) ≤ c (i (c x)):= by -- ic ≤ cic
  intro x
  have h1 := @cl_1 α
  apply h1

theorem lemma_5 : ∀ (x : α), c (i x) ≤ c (i (c x)):= by -- ci ≤ cic
  intro x
  have h1 := @cl_1
  have h2 := @int_3
  have h3 := @cl_3
  apply h3
  apply h2
  apply h1

theorem lemma_6 : ∀ (x : α), c (i (c x)) ≤ c x := by -- cic ≤ c
  intro x
  have h1 := cl_2 c x
  nth_rewrite 2 [← h1]
  apply cl_3
  apply int_1

theorem lemma_7 : ∀ (x : α), i x ≤ id x := by -- i ≤ 1
  intro x
  simp
  apply int_1

theorem lemma_8 : ∀ (x : α), id x ≤ c x := by -- 1 ≤ c
  intro x
  simp
  apply cl_1

theorem lemma_A : ∀ (x : α), i (c x) = i (c (i (c x))) := by -- ic = icic
  intro x
  apply le_antisymm
  have h1 := int_2 i (c x)
  nth_rewrite 1 [← h1]
  apply int_3
  apply cl_1
  apply lemma_6

theorem lemma_B : ∀ (x : α), c (i x) = c (i (c (i x))) := by -- ci = cici
  intro x
  have h1 := cl_2 c (i x)
  apply le_antisymm
  apply lemma_1
  nth_rewrite 2 [← h1]
  apply cl_3
  apply lemma_3

-- equivalence --
theorem theorem_1 : (∀ (x : α), c (i (c x)) ≤ id x) ↔ (∀ (x : α), c (i (c x)) = i x) := by -- cic ≤ 1 ↔ cic = i
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α), c (i (c x)) ≤ x := by
    intro x
    simp at h
    exact h x
  have h2 : c (i (c (i x))) = i x:=by
    apply le_antisymm
    exact h' (i x)
    rw [← lemma_B c i x]
    apply le_trans (lemma_1 c i x)
    apply lemma_3
  have h3 : i (c (i (c x))) = i x:= by
    apply le_antisymm
    apply int_3
    exact h' x
    rw [← lemma_A c i x]
    apply le_trans (lemma_1 c i x)
    apply lemma_2
  have h4 : c (i x) = i (c x) :=by
    rw [lemma_B c i x]
    rw [h2]
    rw [lemma_A c i x]
    exact h3.symm
  rw [← h4]
  have h5 := cl_2 c (i x)
  rw [h5]
  rw [lemma_B c i x]
  exact h2
  -- ← --
  intro h x
  rw [h x]
  apply lemma_7

theorem theorem_2 : (∀ (x : α), id x ≤ c (i (c x))) ↔ (∀ (x : α), c x = c (i (c x))) := by -- 1 ≤ cic ↔ c = cic
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α), x ≤ c (i (c x)) :=by
    intro x
    simp at h
    exact h x
  apply le_antisymm
  have h1 := cl_2 c x
  nth_rewrite 2 [← h1]
  exact h' (c x)
  apply lemma_6
  -- ← --
  intro h x
  rw [← h]
  apply lemma_8

theorem theorem_3 : ((∀ (x : α), i (c x) ≤ c (i x)) ↔ (∀ (x : α),  c (i (c x)) = c (i x))) ∧ ((∀ (x : α), c (i (c x)) = c (i x)) ↔ (∀ (x : α), i (c x) = i (c (i x)))):= by -- ic ≤ ci ↔ (cic = ci ↔ ic =ici
  have h1 : (∀ (x : α), i (c x) ≤ c (i x)) → (∀ (x : α),  c (i (c x)) = c (i x)) := by
    intro h x
    apply le_antisymm
    have h1_2 := cl_2 c (i x)
    rw [← h1_2]
    apply cl_3
    exact h x
    apply lemma_5
  have h2 : (∀ (x : α),  c (i (c x)) = c (i x)) → (∀ (x : α), i (c x) = i (c (i x))) :=by
    intro h x
    rw [lemma_A c i x]
    exact congr_arg i (h x)
  have h3 : (∀ (x : α), i (c x) = i (c (i x))) → (∀ (x : α), i (c x) ≤ c (i x)) :=by
    intro h x
    rw [h x]
    apply lemma_3
  constructor
  constructor
  exact h1
  exact h3 ∘ h2
  constructor
  exact h2
  exact h1 ∘ h3

theorem theorem_4 : (∀ (x : α), i (c x) ≤ id x) ↔ (∀ (x : α), i (c x) = i x) := by -- ic ≤ 1 ↔ ic = i
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α), i (c x) ≤ x :=by
    intro x
    simp at h
    exact h x
  apply le_antisymm
  have h2 := int_2 i (c x)
  rw [← h2]
  apply int_3
  exact h' x
  apply le_trans (lemma_1 c i x)
  apply lemma_2
  -- ← --
  intro h x
  rw [h]
  apply lemma_7

theorem theorem_5 : (∀ (x : α), id x ≤ i (c x)) ↔ (∀ (x : α), c x = i (c x)) := by -- 1 ≤ ic ↔ c = ic
  constructor
  -- → --
  intro h x
  apply le_antisymm
  have h' : ∀ (x : α), x ≤ i (c x) :=by
    intro x
    simp at h
    exact h x
  have h1 := cl_2 c x
  nth_rewrite 2 [← h1]
  exact h' (c x)
  apply le_trans (lemma_4 c i x)
  apply lemma_6
  -- ← --
  intro h x
  rw [← h]
  apply lemma_8

theorem theorem_6 : ((∀ (x : α), c (i x) ≤ i (c x)) ↔ (∀ (x : α), c (i (c x)) = i (c x))) ∧ ((∀ (x : α), c (i (c x)) = i (c x)) ↔ (∀ (x : α), c (i x) = i (c (i x)))) := by -- ci ≤ ic ↔ cic = ic ↔ ci = ici
  have h1 : (∀ (x : α), c (i x) ≤ i (c x)) → (∀ (x : α), c (i (c x)) = i (c x)) := by
    intro h x
    apply le_antisymm
    have h1_1 := cl_2 c x
    nth_rewrite 2 [← h1_1]
    exact h (c x)
    apply lemma_4
  have h2 : (∀ (x : α), c (i (c x)) = i (c x)) → (∀ (x : α), c (i x) = i (c (i x))) :=by
    intro h x
    nth_rewrite 1 [lemma_B c i x]
    exact h (i x)
  have h3 : (∀ (x : α), c (i x) = i (c (i x))) → (∀ (x : α), c (i x) ≤ i (c x)) :=by
    intro h x
    rw [h]
    apply lemma_2
  constructor
  constructor
  exact h1
  exact h3 ∘ h2
  constructor
  exact h2
  exact h1 ∘ h3

theorem theorem_7 : (∀ (x : α), c (i x) ≤ id x) ↔ (∀ (x : α), c (i x) = i x) := by -- ci ≤ 1 ↔ ci =i
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α),  c (i x) ≤ x :=by
    intro x
    simp at h
    exact h x
  apply le_antisymm
  have h1 := int_2 i x
  nth_rewrite 1 [← h1]
  exact h' (i x)
  apply le_trans (lemma_1 c i x)
  apply lemma_3
  -- ← --
  intro h x
  rw [h]
  apply lemma_7

theorem theorem_8 : (∀ (x : α), id x ≤ c (i x)) ↔ (∀ (x : α), c x = c (i x)) := by -- 1 ≤ ci ↔ c = ci
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α), x ≤ c (i x) :=by
    intro x
    simp at h
    exact h x
  apply le_antisymm
  have h2 := cl_2 c (i x)
  rw [← h2]
  apply cl_3
  exact h' x
  apply le_trans (lemma_5 c i x)
  apply lemma_6
  -- ← --
  intro h x
  rw [← h]
  apply lemma_8

theorem theorem_9 : (∀ (x : α), i (c (i x)) ≤ id x) ↔ (∀ (x : α), i (c (i x)) = i x) := by -- ici ≤ 1 ↔ ici = i
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α), i (c (i x)) ≤ x := by
    intro x
    simp at h
    exact h x
  apply le_antisymm
  have h2 := int_2 i x
  nth_rewrite 1 [← h2]
  exact h' (i x)
  apply lemma_1
  -- ← --
  intro h x
  rw [h]
  apply lemma_7

theorem theorem_10 : (∀ (x : α), id x ≤ i (c (i x))) ↔ (∀ (x : α), c x = i (c (i x))) := by -- 1 ≤ ici ↔ c = ici
  constructor
  -- → --
  intro h x
  have h' : ∀ (x : α), x ≤ i (c (i x)) := by
    intro x
    simp at h
    exact h x
  have h2: i (c (i (c x))) = c x := by
    apply le_antisymm
    rw [← lemma_A c i x]
    apply le_trans (lemma_4 c i x)
    apply lemma_6
    exact  h' (c x)
  have h3 : c (i (c (i x))) = c x := by
    apply le_antisymm
    rw [← lemma_B c i x]
    apply le_trans (lemma_5 c i x)
    apply lemma_6
    apply cl_3
    exact h' x
  have h4 : c (i x) = i (c x) := by
    rw [lemma_A c i x]
    rw [h2]
    rw [lemma_B c i x]
    exact h3
  rw [h4]
  have h5 := int_2 i (c x)
  rw [h5]
  rw [lemma_A c i x]
  exact h2.symm
  -- ← --
  intro h x
  rw [← h]
  apply lemma_8
