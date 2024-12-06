import Mathlib.Data.Nat.Prime.Defs

/-!

# Gordon’s Conjectures 1 and 2: Pontryagin–van Kampen duality in the hyperfinite setting
PAVOL ZLATOSˇ


Proposition 2.1.3 concerns the set D - D.
Here we define in general A + B.
-/

instance (X : Type) [Add X] : HAdd (Set X) (Set X) (Set X) := by
  exact {
      hAdd := fun A B ↦ by
        intro x
        exact (∃ y z, y ∈ A ∧ z ∈ B ∧ x = y + z)
  }

theorem add_example : {x : ℕ | x ≤ 1} + {x : ℕ | x ≥ 2} = {x : ℕ | x ≥ 2} := by
  ext x
  constructor
  · intro h
    simp
    obtain ⟨y,hy⟩ := h
    obtain ⟨z,hz⟩ := hy
    simp at hz
    rw [hz.2.2]
    exact le_trans hz.2.1 <|Nat.le_add_left z y
  · intro h
    simp at h
    use 0, x
    simp
    tauto
