import Mathlib.Data.Real.Basic

/-!

# Reverse mathematics, trichotomy, and dichotomy

[Dorais, Hirst and Shafer](http://logicandanalysis.org/index.php/jla/article/view/170)

We formalize Weak König's Lemma in the form of their Theorem 16, item 2:

If α_i^j, i ≤ n_j, j ∈ ℕ is a sequence of finite sequences of reals,
then there is a function h : ℕ → ℕ such that ∀ j ∈ ℕ, ∀ i ≤ n_j, α_{h(j)}^j ≤ α_i^j

Note that the condition `i ≤ n_j` becomes `i : Fin (n j).succ` in Lean,
so item 2 is correct as stated.
-/

lemma least_real {n:ℕ} (α : Fin n.succ → ℝ) : ∃ i, ∀ j, α i ≤ α j := by
induction n with
|zero =>
  use 0;intro j;
  have : j = 0 := by exact Fin.fin_one_eq_zero j
  subst this; exact Preorder.le_refl (α 0)
|succ n hn =>
  obtain ⟨i₀,hi₀⟩ := hn (λ i : Fin n.succ ↦ (α (Fin.castSucc i)))
  by_cases H : α (Fin.last n.succ) ≤ α (Fin.castSucc i₀)
  . use Fin.last n.succ; intro j; by_cases G : j = Fin.last n.succ
    . subst G; apply le_refl
    . calc
      _ ≤ α (Fin.castSucc i₀) := H
      _ ≤ _ := hi₀ (⟨j.1,Fin.val_lt_last G⟩ : Fin n.succ)
  . use Fin.castSucc i₀; intro j; by_cases G : j = Fin.last n.succ
    . subst G; exact le_of_not_ge H
    . exact hi₀ (⟨j.1,Fin.val_lt_last G⟩ : Fin n.succ)

noncomputable def h₀ {n:ℕ} (α : Fin n.succ → ℝ) : { i : Fin n.succ // ∀ j, α i ≤ α j} :=
  Classical.choice (nonempty_subtype.mpr (least_real _))

theorem Weak_Konig's_Lemma (n : ℕ → ℕ) (α : (j:ℕ) → (i : Fin (n j).succ) → ℝ) :
  ∃ h : (j : ℕ) → Fin (n j).succ, ∀ j, ∀ i, α j (h j) ≤ α j i := by
    use λ j ↦ h₀ (α j); intro j i; exact (h₀ (α j)).2 i
