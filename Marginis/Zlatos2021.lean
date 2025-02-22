import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Nat
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fin.Basic

/-!

# Gordon’s Conjectures 1 and 2: Pontryagin–van Kampen duality in the hyperfinite setting

[PAVOL ZLATOS](http://logicandanalysis.org/index.php/jla/article/view/409)


Proposition 2.1.3 concerns the set D - D.
Here we define in general A + B.
-/

instance (X : Type) [Add X] : HAdd (Set X) (Set X) (Set X) := {
      hAdd := fun A B x ↦ (∃ y z, y ∈ A ∧ z ∈ B ∧ x = y + z)
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
