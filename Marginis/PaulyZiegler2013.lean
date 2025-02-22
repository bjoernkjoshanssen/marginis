import Mathlib.Logic.Nonempty
import Mathlib.Tactic.PushNeg

/-

# Relative computability and uniform continuity of relations

[Arno M Pauly, Martin A. Ziegler](http://logicandanalysis.org/index.php/jla/article/view/156)

We formalize their n-fold version of the Henkin quantifier property
and prove it implies an "ordinary" quantifier property.
The converse fails once n is at least 2 and the domain has at least 2 elements.
In that case, we show that one of the four variables can be ignored and the converse still fails.

-/

def Henkin {n:ℕ} {U : Type} (R : (Fin n → U) → (Fin n → U) → Prop) :=
  ∃ Y : Fin n → U → U, ∀ x : Fin n → U, R x (λ k ↦ Y k (x k))

example (R : (Fin n → U) → (Fin n → U) → Prop) :
  Henkin R → ∀ x, ∃ y, R x y := by
  intro ⟨Y,hY⟩ x
  use (λ k ↦ Y k (x k))
  exact hY _

-- How large a domain do we need in order to separate these? n=0 is not enough:

lemma l₀ (x y : Fin 0 → U) : x =y := by
  apply funext
  intro a
  exfalso
  exact Nat.not_succ_le_zero a.1 a.2


lemma l₁ (a x : Fin 0 → U) (R : (Fin 0 → U) → (Fin 0 → U) → Prop) (y : Fin 0 → U):
  R a x → R a y := by
    intro h
    rw [← l₀ x y]
    tauto

lemma zero_not_enough : ¬ ∃ U, ∃ (R : (Fin 0 → U) → (Fin 0 → U) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
    push_neg
    intro U R h
    use (λ k : Fin 0 ↦ False.elim (Nat.not_succ_le_zero k.1 k.2))
    intro x
    obtain ⟨y,hy⟩ := h x
    let Q := l₁ x y R
    apply Q
    tauto

-- n=1 is not enough either. The proof uses Choice:
lemma one_not_enough : ¬ ∃ U, ∃ (R : (Fin 1 → U) → (Fin 1 → U) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
    push_neg
    intro U R h
    use (λ _ x ↦ by
      let V := {y // R (λ _ ↦ x) y}
      have : Nonempty V := by
        exact nonempty_subtype.mpr (h fun _ ↦ x)
      let A := @Classical.choice V this
      exact A.1 0
    )
    intro x
    have h₀ : x = (λ _ ↦ x 0) := by
      apply funext; intro x₁; rw [Fin.fin_one_eq_zero x₁]
    have h₁: (fun k ↦ (Classical.choice (nonempty_subtype.mpr (h fun _ ↦ x k))).1 0) =
    (Classical.choice (nonempty_subtype.mpr (h fun _ ↦ x 0))).1 := by
      apply funext; intro x₁; rw [Fin.fin_one_eq_zero x₁]

    nth_rewrite 1 [h₀]
    rw [h₁]

    exact (Classical.choice (nonempty_subtype.mpr (h fun _ ↦ x 0))).2


-- n=2 may be enough, but not if U has only one element:
example : ¬ ∃ (R : (Fin n → Unit) → (Fin n → Unit) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
    intro hc
    obtain ⟨R,hR⟩ := hc
    revert hR
    simp
    intro h
    exists (λ _ ↦ by
      intro; exact ()
    )
    intro x
    simp
    obtain ⟨_,hy⟩ := h x
    tauto

-- n=2 is enough with U having two elements. We can even ignore one of the variables (`y 1` below) completely.
example : ∃ (R : (Fin 2 → Bool) → (Fin 2 → Bool) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
  use (λ x y ↦  y 0 = xor (x 0) (x 1)
  )
  constructor
  . intro x
    use (λ _ ↦ xor (x 0) (x 1))
  unfold Henkin
  push_neg
  intro Y
  by_cases H: (Y 0 false = false)
  . use (λ k ↦ ite (k=0) false true);simp;tauto
  . use (λ k ↦ ite (k=0) false false);simp;aesop
