import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic
-- import Mathlib.Order.Defs
import Mathlib.Order.Sublattice
-- import Mathlib.Data.Real.Hyperreal
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!

# Lattice tables
as used in computability theory. -/

structure latticeTable (A : Type*) where
  (Θ : Set <| A → A → Prop)
  (h : (fun _ _ => True) ∈ Θ ∧
       (fun x y => x=y) ∈ Θ ∧
    (∀ α ∈ Θ, ∀ β ∈ Θ, (fun x y => α x y ∧ β x y) ∈ Θ) ∧
    (∀ α ∈ Θ, ∀ β ∈ Θ, Relation.Join (Relation.ReflTransGen  (fun x y => α x y ∨ β x y)) ∈ Θ) ∧ -- need eq. closure
    ∀ α ∈ Θ, IsEquiv _ α)

lemma Relation_Transgen_refl {A : Type*} {R : A → A → Prop}
    (h : Reflexive R):
    Reflexive (Relation.TransGen R) := by
  intro x
  exact Relation.TransGen.single (h x)

lemma Relation_Transgen_symm {A : Type*} {R : A → A → Prop}
    (h : Symmetric R):
    Symmetric (Relation.TransGen R) := fun x y h₁ => by
  induction h₁ with
  | single h₂ =>
    apply Relation.TransGen.single
    exact h h₂
  | tail _ f e =>
    exact Relation.TransGen.head (h (h (h f))) e



/-- Get lattice representations as IsSubLattice of this: -/
instance (A : Type*) : Lattice {α : A → A → Prop // IsEquiv _ α} := {
  le := fun α β => ∀ x y : A, β.1 x y → α.1 x y
  lt := fun α β =>
      (∀ x y : A, β.1 x y → α.1 x y) ∧
    ¬ (∀ x y : A, α.1 x y → β.1 x y)
  sup := fun α β => ⟨fun x y => α.1 x y ∧ β.1 x y, {
        refl := fun _ => ⟨α.2.refl _, β.2.refl _⟩
        trans := by
            have := α.2.trans
            have := β.2.trans
            tauto
        symm := fun _ _ h => ⟨α.2.symm _ _ h.1, β.2.symm _ _ h.2⟩
    }⟩
  le_refl := by simp
  le_trans := by simp_all
  le_antisymm  := fun α β h₀ h₁ => by aesop
  le_sup_left  := fun _ _ _ _ h => h.1
  le_sup_right := fun _ _ _ _ h => h.2
  sup_le       := fun _ _ _ _ _ => by aesop
  inf := fun α β => ⟨Relation.TransGen fun x y => α.1 x y ∨ β.1 x y,
    {
        refl := fun a => by
            have := α.2.refl
            have := @Relation_Transgen_refl A (fun x y ↦ α.1 x y ∨ β.1 x y)
                (fun x => Or.inl <| α.2.refl x)
            apply this
        trans := fun _ _ _ => Relation.TransGen.trans
        symm := by
            apply Relation_Transgen_symm
            have := α.2.symm
            have := β.2.symm
            tauto
    }⟩
  inf_le_left  := fun _ _ _ _ h => Relation.TransGen.single <| Or.inl h
  inf_le_right := fun _ _ _ _ h => Relation.TransGen.single <| Or.inr h
  le_inf := fun α _ _ _ _ _ _ h => by
    have := α.2.trans
    induction h <;> tauto
}

def 𝓢 (f : ℕ → ℕ) := Σ n, Π i : Fin n, Fin <| f i.1

def σ : 𝓢 (fun k => k.succ) := ⟨2,
  by intro i;convert i;sorry
  -- fun i => i
  ⟩



def mysublattice : Sublattice ({α : Fin 2 → Fin 2 → Prop // IsEquiv _ α}) := {
    carrier := by
        exact Set.univ
    infClosed' := by exact fun ⦃a⦄ a ⦃b⦄ _ ↦ a
    supClosed' := by exact fun ⦃a⦄ a ⦃b⦄ _ ↦ a

}

-- instance (A : Type*) (T : latticeTable A) : Lattice T.Θ := {
--   le := fun α β => ∀ x y : A, β.1 x y → α.1 x y
--   sup := fun α β => ⟨fun x y => α.1 x y ∧ β.1 x y, T.h.2.2.1 _ α.2 _ β.2⟩
--   le_refl := fun α x y => id
--   le_trans := fun α β γ h₀ h₁ => by
--     unfold LE.le at *
--     simp_all
--   le_antisymm := fun α β => sorry
--   le_sup_left := sorry
--   le_sup_right := sorry
--   sup_le := sorry
--   inf := sorry
--   inf_le_left := sorry
--   inf_le_right := sorry
--   le_inf := sorry
--   lt_iff_le_not_le := sorry
-- }

/-- The 0-1 lattice is a lattice table. -/
def smallLatTab {A : Type*} : latticeTable A := by
  exact {
    Θ := fun α => α = (fun _ _ => True) ∨ α = (fun x y => x=y)
    h := by
      constructor
      · left
        rfl
      · constructor
        · right
          rfl
        · constructor
          · intro α hα β hβ
            cases hα with
            | inl h =>
              cases hβ with
              | inl g => subst h;subst g;left;simp
              | inr g => subst h;subst g;right;simp
            | inr h =>
              rcases hβ with (g | g) <;> (subst h;subst g;right;simp)
          · constructor
            · intro α hα β hβ
              cases hα with
              | inl h =>
                cases hβ with
                | inl g =>
                  subst h;subst g;left;simp
                  ext x y
                  simp
                  use x
                  constructor
                  · exact Relation.ReflTransGen.refl
                  · exact Relation.ReflTransGen.single trivial
                | inr g =>
                  subst h;subst g
                  left;simp
                  ext x y
                  simp
                  use x
                  constructor
                  · exact Relation.ReflTransGen.refl
                  · exact Relation.ReflTransGen.single trivial
              | inr h =>
                cases hβ with
                | inl g =>
                  subst h;subst g
                  left;simp
                  ext x y
                  simp
                  use x
                  constructor
                  · exact Relation.ReflTransGen.refl
                  · exact Relation.ReflTransGen.single trivial
                | inr g =>
                  subst h;subst g
                  right;simp
                  ext x y
                  constructor
                  · have : Relation.ReflTransGen (fun x y : A ↦ x = y) =
                      (fun x y ↦ x = y) := by
                        sorry
                        -- refine Relation.reflTransGen_eq_self (congrFun rfl) ?trans
                        -- exact transitive_of_trans fun x y ↦ x = y
                    rw [this]
                    intro h
                    obtain ⟨z,hz⟩ := h
                    simp at hz
                    aesop
                  · intro h
                    subst h
                    use x
            · intro α hα
              cases hα with
              | inl h =>
                subst h
                exact {
                  symm := by intros;trivial
                  refl := by intros;trivial
                  trans := by intros;trivial
                }
              | inr h =>
                subst h
                exact eq_isEquiv A
  }


/-- The partition lattice is a lattice table. -/
def Partition {A : Type*} : latticeTable A := by
  exact {
    Θ := fun α => IsEquiv _ α
    h := by
      constructor
      · exact {
          symm := fun _ _ => id
          refl := fun _ => trivial
          trans := fun _ _ _ _ => id
        }
      · constructor
        · exact {
            symm := fun _ _    => Eq.symm
            refl :=               Eq.refl
            trans := fun _ _ _ => Eq.trans
          }
        · constructor
          · exact fun α hα β hβ => {
            symm := fun a b h => ⟨hα.symm a b h.1,
                                  hβ.symm a b h.2⟩
            refl := fun _ => ⟨hα.refl _, hβ.refl _⟩
            trans := fun a b c hab hbc => ⟨hα.trans _ _ _ hab.1 hbc.1,
                                           hβ.trans _ _ _ hab.2 hbc.2⟩
            }
          · constructor
            · intro α hα β hβ
              have hs : Symmetric fun x y ↦ α x y ∨ β x y := by
                intro u v huv
                cases huv with
                | inl h =>
                  left
                  exact hα.symm u v h
                | inr h =>
                  right
                  exact hβ.symm u v h
              exact {
                symm := fun _ _ ⟨c,hc⟩ => ⟨c, hc.symm⟩
                refl := fun a => by use a
                trans := fun a b c ⟨c₀,hc₀⟩ ⟨c₁,hc₁⟩ =>
                  sorry --⟨c₀, ⟨hc₀.1, hc₁.2.trans <| (hc₁.1.symmetric hs).trans hc₀.2⟩⟩
              }
            · exact fun _ => id
  }

def End {A : Type*} (L : latticeTable A) (f : A → A) : Prop :=
  ∀ α ∈ L.Θ, ∀ x y, α x y → α (f x) (f y)



/-- Every function is an endomorphism of the {0,1} lattice. -/
example {A : Type*} (f : A → A) : End smallLatTab f := by
  intro α hα x y h₀
  cases hα with
  | inl h =>
    subst h;trivial
  | inr h =>
    subst h
    rw [h₀]

def principal {A : Type*} (a b : A) : A → A → Prop :=
    fun x y => x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

def principal_preserving {A : Type*} (f : A → A) : Prop :=
  ∀ a b, ∀ x y, principal a b x y → principal a b (f x) (f y)

/-- We now prove every endomorphism of Part n is identity or constant, unless n ≤ 2. -/
lemma principal_is_equiv {A : Type*} (a b : A) : IsEquiv A (principal a b) :=
  {
      symm  := by unfold principal;tauto
      refl  := by tauto
      trans := by
        unfold principal;
        intro u v w h₀ h₁
        cases h₀ with
        | inl h => subst h;tauto
        | inr h =>
          rcases h with h | h <;> (
            have := h.1
            subst this
            have := h.2
            subst this
            tauto)
  }

lemma principal_preserving_id {A : Type*} : @principal_preserving A id :=
  fun _ _ _ _ => id

lemma End_Partition_id {A : Type*} : @End A Partition id := by
  intro a _ x y
  simp

lemma End_Partition_const {A : Type*} (c : A) : @End A Partition (fun _ => c) := by
  intro α hα x y _
  simp
  apply hα.refl

lemma const_iff {A : Type*} (f : A → A) :
    (∀ c, ∃ x, f x ≠ c) ↔ (∀ c, f ≠ fun _ => c) := by
  constructor
  · intro h c hc
    subst hc
    specialize h c
    simp at h
  · intro h c
    specialize h c
    contrapose h
    ext x
    aesop


lemma not_id_or_const {A : Type*} {f : A → A} (hf₀ : f ≠ id) (hf₁ : ∀ c, f ≠ fun _ => c) :
  ∃ a b, a ≠ f a ∧ f a ≠ f b := by
    rw [← const_iff] at hf₁
    obtain ⟨a,ha⟩ : ∃ a, f a ≠ a := by
      contrapose hf₀
      push Not at hf₀
      ext a
      rw [hf₀ a]
      rfl
    use a
    have := hf₁ (f a)
    obtain ⟨b,hb⟩ := this
    use b
    tauto

lemma end_aux₀ {A : Type*} {f : A → A} {a b : A} (h : a ≠ f a ∧ f a ≠ f b)
    (hf : End Partition f) : f a = b ∧ f b = a := by
  specialize hf (principal a b) (principal_is_equiv _ _) a b (by tauto)
  unfold principal at hf
  tauto

lemma end_aux₀p {A : Type*} {f : A → A} {a b : A}  (h : a ≠ f a ∧ f a ≠ f b)
    (hf : principal_preserving f) : f a = b ∧ f b = a := by
  specialize hf a b a b (by
    unfold principal
    right;left;tauto
  )
  unfold principal at hf
  tauto

lemma end_aux₁ {A : Type*} {f : A → A} {a b c : A} (h : a ≠ f a ∧ f a ≠ f b)
    (hf : End Partition f) (h₂ : a ≠ c) : f c = a := by
  have := end_aux₀ h hf
  specialize hf (principal b c) (principal_is_equiv _ _) b c (by tauto)
  unfold principal at hf
  aesop

lemma end_aux₁p {A : Type*} {f : A → A} {a b c : A}  (h : a ≠ f a ∧ f a ≠ f b)
    (hf : principal_preserving f) (h₂ : a ≠ c) : f c = a := by
  have := end_aux₀p h hf
  specialize hf b c b c (by
    unfold principal
    right;left;tauto
  )
  unfold principal at hf
  cases hf with
  | inl h => rw [h] at this;tauto
  | inr h =>
  cases h with
  | inl h₀ => exfalso;have h₂ := h.2;apply h₂;apply this.1.trans;tauto
  | inr h₀ => aesop


lemma not_endo {A : Type*} {f : A → A} {a b c : A} (h : a ≠ f a ∧ f a ≠ f b)
    (h₂ : a ≠ c) (h₄ : b ≠ c) : ¬ End Partition f := by
  intro hf
  have := end_aux₀ h hf
  have h₃ : f c = a := by apply end_aux₁ <;> tauto
  specialize hf (principal a c) (principal_is_equiv _ _) a c (by tauto)
  unfold principal at hf
  aesop

lemma not_pp {A : Type*} {f : A → A} {a b c : A} (h : a ≠ f a ∧ f a ≠ f b)
    (h₂ : a ≠ c) (h₄ : b ≠ c) : ¬ principal_preserving f := by
  intro hf
  have := end_aux₀p h hf
  have h₃ : f c = a := by apply end_aux₁p <;> tauto
  specialize hf a c a c
  unfold principal at hf
  aesop

open Classical
theorem getThree_fin {A : Type*} [Fintype A] (hn : Fintype.card A ≥ 3) (a b : A) :
    ∃ c, a ≠ c ∧ b ≠ c := by
  by_contra H
  have : ¬ Fintype.card A ≤ 2 := by omega
  apply this
  have : Finset.univ ⊆ {a,b} := by
    intro c _
    push_neg at H
    specialize H c
    simp
    tauto
  have : Finset.card {a,b} ≤ 2 := Finset.card_le_two
  aesop

lemma getThree_inf {A : Type*} [Infinite A] : ∃ g₀ g₁ g₂ : A, g₀ ≠ g₁ ∧ g₁ ≠ g₂ ∧ g₀ ≠ g₂ := by
  let g := Infinite.natEmbedding A
  have hg : Function.Injective g := Function.Embedding.injective g
  have : g 0 ≠ g 1 := by
    intro hc
    specialize hg hc
    simp at hg
  have : g 1 ≠ g 2 := by
    intro hc
    specialize hg hc
    simp at hg
  have : g 0 ≠ g 2 := by
    intro hc
    specialize hg hc
    simp at hg
  use g 0
  use g 1
  use g 2

theorem clone_of_pp_of_ge_three {A : Type*} [Fintype A] (hn : Fintype.card A ≥ 3)
    (f : A → A) (hf : principal_preserving f) :
    f = id ∨ ∃ c, f = fun _ => c := by
  contrapose hf
  push_neg at hf
  obtain ⟨a,b,hab⟩ := not_id_or_const hf.1 hf.2
  obtain ⟨c,hc⟩ := getThree_fin (by aesop) a b
  exact not_pp hab hc.1 hc.2

theorem clone_of_pp_of_inf {A : Type*} [Infinite A] {f : A → A} (hf : principal_preserving f) :
    f = id ∨ ∃ c,f = fun _ => c := by
  contrapose hf
  push_neg at hf
  obtain ⟨a,b,hab⟩ := not_id_or_const hf.1 hf.2
  obtain ⟨g₀,g₁,g₂,hg⟩ := @getThree_inf A _
  have := @not_pp A f a b
  obtain ⟨a,b,hab⟩ := not_id_or_const hf.1 hf.2
  obtain ⟨c,hc⟩ : ∃ c, a ≠ c ∧ b ≠ c := by
    by_cases h₀ : a = g₀
    · by_cases h₁ : b = g₁
      · use g₂
        aesop
      · use g₁
        aesop
    · by_cases h₁ : b = g₁
      · use g₀
        aesop
      · by_cases h₂ : b = g₀
        · by_cases h₃ : a = g₁
          · subst h₂ h₃;use g₂;tauto
          · use g₁
        · use g₀

  have := @not_pp A f a b c hab hc.1 hc.2

  apply this

/-- Endomorphisms of the Partition lattice. -/
theorem pp_of_EndPart {A : Type*} (f : A → A) (hf : End Partition f) : principal_preserving f := by
  unfold End Partition at hf
  unfold principal_preserving
  intro a b
  exact hf (principal a b) (principal_is_equiv _ _)

/-- This is not used, but seems useful. -/
lemma get_two {A : Type*} [Fintype A] (h : Fintype.card A ≥ 2) :
  ∃ a b : A, a ≠ b := by
    contrapose h
    push_neg at h ⊢
    refine Nat.lt_add_one_of_le ?_
    refine Fintype.card_le_one_iff.mpr ?_
    exact h


lemma getCases {A : Type*} [Fintype A] {u₀ u₁ : A} (hu : Finset.univ = {u₀, u₁}) (a : A) :
    a = u₀ ∨ a = u₁ := by
        have ha : a ∈ (Finset.univ) := Finset.mem_univ a
        rw [hu, Finset.mem_insert, Finset.mem_singleton] at ha
        exact ha

/-- This long easy proof shows that for n=2 we do have an endomorphism
of Part that's not in the clone. -/
theorem ne_two_of_EndPart_implies_clone {A : Type*} [Fintype A] : (∀ f : A → A, End Partition f →
  f = id ∨ ∃ c, f = fun _ => c) → Fintype.card A ≠ 2 := by
  intro h
  contrapose h
  push Not
  obtain ⟨a,b,hu⟩ := Finset.card_eq_two.mp <| (@Finset.card_univ A _) ▸ h

  use (fun x => ite (x=a) b (ite (x=b) a x))
  constructor
  · intro α hα x y hxy
    have hy := getCases hu.2 y
    cases getCases hu.2 a with
    | inl h =>
      cases getCases hu.2 b with
      | inl h =>
        subst h
        tauto
      | inr h =>
        cases getCases hu.2 x with
        | inl h =>
          subst h
          simp
          cases hy with
          | inl h =>
            subst h
            simp
            apply hα.refl
          | inr h =>
            subst h
            simp
            rw [if_neg (by tauto)]
            apply hα.symm
            exact hxy
        | inr h =>
          subst h
          simp
          cases hy with
          | inl h =>
            subst h
            simp_all
            apply hα.symm
            exact hxy
          | inr h =>
            subst h
            simp_all
            apply hα.refl
    | inr h =>
      subst h
      simp
      tauto
  · constructor
    · intro hc
      apply congrFun at hc
      have ha := hc a
      simp at ha
      tauto
    · intro c
      suffices ∃ d,
        (fun x ↦ if x = a then b else if x = b then a else x) d ≠ (fun _ ↦ c) d by
        contrapose this
        push Not
        intro d
        apply congrFun at this
        rw [this]
      use c
      have h₀ : (Finset.univ : Finset A).card = 2 := by aesop
      have h₁ := Finset.card_eq_two.mp h₀
      obtain ⟨u₀,u₁,hu⟩ := h₁

      have : c = a ∨ c = b := by
        rcases getCases hu.2 a with (h | h) <;> (
          rcases getCases hu.2 c with (h₀ | h₀) <;> (
            subst h h₀
            have := getCases hu.2 b
            tauto
          ))
      rcases this with (h | h) <;> (subst h;simp;tauto)

theorem clone_of_pp_of_ne_two {A : Type*} [Fintype A] : Fintype.card A ≠ 2 → ∀ f : A → A, principal_preserving f →
  f = id ∨ ∃ c, f = fun _ => c := by
  intro h
  by_cases hn : Fintype.card A ≥ 3
  · exact fun f a ↦ clone_of_pp_of_ge_three hn f a
  · intro f _
    left
    have : Fintype.card A = 0 ∨ Fintype.card A = 1 := by omega
    cases this with
    | inl h =>
      ext x
      exfalso;revert h
      have : Nonempty A := by
        use x
      refine Fintype.card_ne_zero
    | inr h =>
      obtain ⟨u,hu⟩ := Fintype.card_eq_one_iff.mp h
      ext x
      aesop

lemma ne_two_iff_pp_implies_clone_of_fin {A : Type*} [Fintype A] : Fintype.card A ≠ 2 ↔ ∀ f : A → A, principal_preserving f → f = id ∨ ∃ c, f = fun _ => c := by
  constructor
  · apply clone_of_pp_of_ne_two
  · exact fun h => ne_two_of_EndPart_implies_clone fun f hf => h f (pp_of_EndPart f hf)

lemma ne_two_iff_EndPart_implies_clone_of_fin {A : Type*} [Fintype A] : Fintype.card A ≠ 2 ↔
  ∀ f : A → A, End Partition f → f = id ∨ ∃ c, f = fun _ => c := by
  constructor
  · exact fun h f hf => (ne_two_iff_pp_implies_clone_of_fin).mp h f <| pp_of_EndPart f hf
  · apply ne_two_of_EndPart_implies_clone


theorem EndPart_of_clone {A : Type*} (f : A → A) :
    (f = id ∨ ∃ c, f = fun _ ↦ c) → End Partition f := by
  · intro h
    cases h with
    | inl h => exact fun _ _ _ _ => h ▸ id
    | inr h =>
      obtain ⟨c,hc⟩ := h
      intro _ hα _ _ _
      subst hc
      apply hα.refl

theorem pp_eq_clone_of_ne_two {A : Type*} [Fintype A] (hn : Fintype.card A ≠ 2) :
    principal_preserving = fun f : A → A => f = id ∨ ∃ c, f = fun _ => c := by
  ext f
  constructor
  · exact ne_two_iff_pp_implies_clone_of_fin.mp (by aesop) f
  · exact fun h => pp_of_EndPart f <| EndPart_of_clone f h

theorem EndPart_eq_clone_of_ne_two {A : Type*} [Fintype A] (hn : Fintype.card A ≠ 2) :
  End Partition = fun f : A → A => f = id ∨ ∃ c, f = fun _ => c := by
  ext f
  constructor
  · exact ne_two_iff_EndPart_implies_clone_of_fin.mp (by aesop) f
  · exact EndPart_of_clone _

theorem eq_of_neg_two {A : Type*} [Fintype A]
    {α : A → A → Prop} (hα : IsEquiv A α) {a b : A}
    (hab : a ≠ b ∧ Finset.univ = {a, b}) (H : ¬ α a b) : α = Eq := by
  ext x y
  have := hα.refl a
  have := hα.refl b
  have := hα.symm a b
  have := hα.symm b a
  cases getCases hab.2 x with
  | inl h =>
    subst h
    cases getCases hab.2 y with
    | inl h =>
      subst h
      simp
      apply hα.refl
    | inr h =>
      subst h
      tauto
  | inr h =>
    subst h
    cases getCases hab.2 y with
    | inl h =>
      subst h
      simp_all
      tauto
    | inr h =>
      subst h
      tauto

theorem all_of_pos_two {A : Type*} [Fintype A]
    {α : A → A → Prop} (hα : IsEquiv A α) {a b : A}
    (hab : a ≠ b ∧ Finset.univ = {a, b}) (H : α a b) (u v : A) : α u v := by
  cases getCases hab.2 u with
  | inl h =>
    subst h
    cases getCases hab.2 v with
    | inl h =>
      subst h
      apply hα.refl
    | inr h => subst h;exact H
  | inr h =>
    subst h
    cases getCases hab.2 v with
    | inl h =>
      subst h
      apply hα.symm _ _ H
    | inr h =>
      subst h
      apply hα.refl

/-- For the special case `n=2` we check directly that EndPart_eq_pp. -/
theorem EndPart_eq_pp_of_two {A : Type*} [inst : Fintype A] (hn : Fintype.card A = 2) :
    End Partition = @principal_preserving A := by
  · ext f
    constructor
    · exact fun h a b => h (principal a b) (principal_is_equiv a b)
    · intro _ α hα x y hxy
      obtain ⟨a,b,hab⟩ := Finset.card_eq_two.mp <| (@Finset.card_univ A _) ▸ hn
      by_cases H : α a b
      · apply all_of_pos_two <;> tauto
      · have : α = fun x y => x = y := by apply eq_of_neg_two <;> tauto
        subst this hxy
        simp
/-- On a finite set, a function preserves all equivalence relations iff it preserves all principal ones. -/
lemma EndPart_eq_pp_of_fin {A : Type*} [Fintype A] : End Partition = @principal_preserving A := by
  by_cases hn : Fintype.card A = 2
  · exact EndPart_eq_pp_of_two hn
  · exact (EndPart_eq_clone_of_ne_two hn).trans (pp_eq_clone_of_ne_two hn).symm

theorem pp_eq_clone_of_inf {A : Type*} (hn : Infinite A) :
    principal_preserving = fun f : A → A => f = id ∨ ∃ c, f = fun _ => c := by
  ext f
  constructor
  · exact clone_of_pp_of_inf
  · intro h
    cases h with
    | inl h =>
      subst h
      intro a b x y h₀
      simp_all
    | inr h =>
      obtain ⟨c,hc⟩ := h
      intro a b x y _
      have hc : ∀ x, f x = c := by aesop
      rw [hc x, hc y]
      unfold principal
      tauto

/-- The main result: being an endomorphism of the partition lattice is equivalent
to being principal-congruence preserving, on any set. -/
theorem EndPart_eq_pp {A : Type*} : End Partition = @principal_preserving A := by
  by_cases H : ∃ _ : Fintype A, True
  · obtain ⟨_, _⟩ := H
    exact EndPart_eq_pp_of_fin
  · have hI : Infinite A := by
      by_contra H₀
      have := fintypeOfNotInfinite H₀
      push Not at H
      apply H
      exact this
    obtain ⟨g₀,g₁,_,_⟩ := @getThree_inf A _
    ext f
    constructor
    · intro he
      cases clone_of_pp_of_inf (pp_of_EndPart f he) with
      | inl h => subst h; apply principal_preserving_id
      | inr h =>
        obtain ⟨c,hc⟩ := h
        subst hc
        intro _ _ _ _ _
        exact Or.symm (Or.inr rfl)
    · intro h
      have : f = id ∨ ∃ c, f = fun _ => c := by
        have := pp_eq_clone_of_inf hI
        rw [this] at h
        tauto
      cases this with
      | inl h =>
        subst h
        apply End_Partition_id
      | inr h =>
        obtain ⟨c,hc⟩ := h
        have : f = fun _ => c := by ext x;simp_all
        subst this
        apply End_Partition_const


def smul' {k : ℕ} (c : ℝ) (a : Fin k → ℝ) : Fin k → ℝ := fun i => c * a i

-- theorem linear_logic_equation (a : Fin 2 → ℝ) (b : Fin 3 → ℝ) (v : Fin 5 → ℝ) :
--     (∀ c d : ℝ, Matrix.dotProduct (smul' c a) ![v 0, v 1]
--                   + Matrix.dotProduct (smul' d b) ![v 2, v 3, v 4] = 0) ↔
--     ∃ p q, Matrix.dotProduct p a = 0
--          ∧ Matrix.dotProduct q b = 0 ∧ v = ![p 0, p 1, q 0, q 1, q 2] := by
--   constructor
--   · intro h
--     use ![v 0, v 1], ![v 2, v 3, v 4]
--     simp_all [smul', Matrix.dotProduct, Finset.sum]
--     constructor
--     · rw [← h 1 0]
--       ring
--     · constructor
--       rw [← h 0 1]
--       ring
--       · ext x
--         fin_cases x <;> rfl
--   · intro ⟨p,q,h⟩ c d
--     have := h.2.2
--     subst this
--     unfold smul' Matrix.dotProduct Finset.sum at *
--     simp_all
--     ring_nf
--     have : c * a 0 * p 0 + c * a 1 * p 1 + d * b 0 * q 0 + d * b 1 * q 1 + d * b 2 * q 2
--          = c * (a 0 * p 0 + a 1 * p 1)   + d * (b 0 * q 0 + b 1 * q 1 + b 2 * q 2) := by ring
--     rw [this]
--     simp [mul_comm] at h -- !
--     rw [h.1]
--     simp
--     rw [← h.2]
--     ring_nf
--     tauto

-- lemma great {k : ℕ} (c : ℝ) (a p : Fin k → ℝ) :
--     Matrix.dotProduct (c • a) p = c * Matrix.dotProduct a p := by
--   unfold Matrix.dotProduct
--   simp
--   simp_rw [mul_assoc]
--   exact Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ a i * p i) c)

-- example (a : ℝ) (b : Fin 2 → ℝ) : smul' a b = a • b := by
--   unfold smul'
--   symm
--   rfl

open Matrix -- needed for ⬝ᵥ

lemma finfin {k l : ℕ} (v₀ : Fin k → ℝ) (v₁ q : Fin l → ℝ)
    (H : Fin.append v₀ v₁ = Fin.append v₀ q) :
    v₁ = q := by
      ext i
      have : v₁ i = Fin.append v₀ v₁ (Fin.natAdd k i) := by simp
      rw [this, H]
      simp

lemma nifnif {k l : ℕ} (v₀ : Fin k → ℝ) (v₁ : Fin l → ℝ) (p : Fin k → ℝ)
  (q : Fin l → ℝ)
  (H : Fin.append v₀ v₁ = Fin.append p q) : v₀ = p := by
      ext i
      have : v₀ i = Fin.append v₀ v₁ (Fin.castAdd l i) := by simp
      rw [this, H]
      simp

/--
1-dimensional subspaces version of:
(A ⊕ B)^⊥ = A^⊥ ⊕ B^⊕
(v is ⊥ to anything in A ⊕ B) ↔ (v is in the span of some p ∈ A⊥ and some q ∈ B⊥)
-/
theorem linear_logic_equation' {k l : ℕ}
    (a : Fin k → ℝ) (b : Fin l → ℝ) (v₀ : Fin k → ℝ) (v₁ : Fin l → ℝ) :
    (∀ c d : ℝ, c • a ⬝ᵥ v₀
              + d • b ⬝ᵥ v₁ = 0) ↔
    ∃ p q, p ⬝ᵥ a = 0
         ∧ q ⬝ᵥ b = 0 ∧ Fin.append v₀ v₁ = Fin.append p q := by
  constructor
  · intro h
    use v₀, v₁
    simp_all [dotProduct, Finset.sum]
    constructor
    · rw [← h 1 0]
      ring_nf
      simp
      simp_rw [mul_comm]
    · rw [← h 0 1]
      ring_nf
      simp
      simp_rw [mul_comm]
  · intro ⟨p,q,h⟩ c d
    have H := h.2.2
    have : v₀ = p := by
      apply nifnif; exact H
    subst this
    have : v₁ = q := by
      apply finfin; exact H
    subst this
    sorry
    -- rw [great,great]
    -- nth_rewrite 1 [dotProduct_comm]
    -- nth_rewrite 2 [dotProduct_comm]
    -- rw [h.1, h.2.1]
    -- simp

/--
(A ⊕ B)^⊥ = A^⊥ ⊕ B^⊕
(v is ⊥ to anything in A ⊕ B) ↔ (v is in the span of some p ∈ A⊥ and some q ∈ B⊥)
because both just say that v = Fin.append v₀ v₁
where v₀ ∈ A^⊥ and v₁ ∈ B^⊥.
-/
theorem linear_logic_equation'' {k l : ℕ}
    (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ))
    [Nonempty A] [Nonempty B]
    (v₀ : Fin k → ℝ) (v₁ : Fin l → ℝ) :
    (∀ c d : ℝ, ∀ a ∈ A, ∀ b ∈ B, c • a ⬝ᵥ v₀ -- this has vector addition
              + d • b ⬝ᵥ v₁ = 0) ↔
    ∀ a ∈ A, ∀ b ∈ B, ∃ p q,
           p ⬝ᵥ a = 0 -- this does not (on its face)
         ∧ q ⬝ᵥ b = 0 ∧ Fin.append v₀ v₁ = Fin.append p q := by
    constructor
    · intro h a ha b hb
      use v₀, v₁
      have h₀ := h 0 1 a ha b hb
      have h₁ := h 1 0 a ha b hb
      simp at h₀ h₁
      constructor
      · rw [← h₁]
        rw [dotProduct_comm]
      · constructor
        · rw [← h₀]
          rw [dotProduct_comm]
        · rfl
    · intro h c d a ha b hb
      specialize h a ha b hb
      obtain ⟨p,q,hpq⟩ := h
      have : v₀ = p := by
        apply nifnif
        exact hpq.2.2
      subst this
      have : v₁ = q := by
        apply finfin
        exact hpq.2.2
      subst this
      simp [dotProduct_comm]
      rw [hpq.1, hpq.2.1]
      simp


/-- It begins... Feb 16, 2025


The focal lengths are those at which we "clear the level"
(at the next level they have to agree with `x`):

      `01101` 01110
          \  /
0100 0101 `0110` 0111   4
  \  /      \    /
   010     `011`
      \    /
  00   `01`            2
   \  /
   `0`     1           1
     \   /
      `∅`              0
-/
def x : Fin 5 → Fin 2 := ![0,1,1,0,1]
def focalLength : Fin 5 → Fin 6 := ![0,1,2,4,5]
-- should be a set, to automatize that it's "increasing" and injective.

def focalLen : Set (Fin 6) := {0,1,2,4,5}

/-- The domain is determined by the "current approximation " `z`
and the set of focal lengths.
-/
def lensDomain {s : ℕ} (z : Fin s → Fin 2) (focLen : Set (Fin s.succ)) (l : ℕ) :
    Set (Fin l → Fin 2) := {σ |
  ∀ f ∈ focLen, (h : f.1 < l) → ∀ j : Fin f, σ ⟨j.1, by omega⟩
                                           = z ⟨j.1, by omega⟩}

def rangeLengths : Fin 6 → ℕ := ![0,5,7,8,9,11]



-- /-- A particular example of a tree for `x` and `focalLen` -/
-- def T (k : Fin 6) (σ : lensDomain x focalLen k.1) :
-- -- Lerman does not use "lens domain" but it goes well with "focal point".
-- -- equivalently:
-- -- def T (k : Fin 6) (σ : { τ : Fin k.1 → Fin 2 // τ ∈ lensDomain x focalLen k.1}) :
--     Fin (rangeLengths k) → Fin 2 := by
--   by_cases h₀ : k = 0
--   · subst h₀
--     intro i
--     unfold rangeLengths at i
--     have := i.2
--     simp at this -- in other words T(∅)=∅
--   · by_cases h₁ : k = 1
--     · subst h₁
--       unfold rangeLengths
--       by_cases h₂ : σ.1 ⟨0,by omega⟩ = 0
--       · exact ![0,0,0,0,0] -- in other words T(⟨0⟩)=⟨0,0,0,0,0⟩
--       · exact ![1,0,1,1,1] -- in other words T(⟨1⟩)=⟨1,0,1,1,1⟩
--     by_cases h₂ : k = 2
--     · subst h₂
--       by_cases g₀ : σ.1 ⟨0,by omega⟩ = 0
--       by_cases h₃ : σ.1 = ![0,0]
--       exact ![0,0,0,0,0,0,1]
--       by_cases h₅ : σ.1 = ![0,1]
--       exact ![0,0,0,0,0,1,1]
--       by_cases h₄ : σ.1 ⟨1,by omega⟩ = 0
--       · exfalso
--         contrapose h₃
--         simp
--         ext l
--         fin_cases l
--         . simp at g₀ ⊢
--           rw [g₀]
--           simp
--         · rw [h₄]
--           simp
--       exfalso
--       apply h₅
--       ext u
--       fin_cases u
--       · simp at g₀ ⊢

--         rw [g₀]
--         simp
--       simp at h₄ ⊢
--       have : (σ.1 ⟨1,by omega⟩).1 = 0 ∨ (σ.1 ⟨1,by omega⟩).1 = 1 := by omega
--       cases this with
--       | inl h => simp at h;exfalso;apply h₄;exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h)))
--       | inr h => simp at h;exact h
--       have : σ.1 ⟨1,by omega⟩ = 1 := sorry

--       by_cases h₃ : σ.1 = ![1,0]
--       · rw [h₃] at *
--         have h := σ.2
--         unfold lensDomain at h
--         -- simp at h
--         specialize h 1 (by simp [focalLen]) (by simp) ⟨0,by simp⟩
--         unfold x at h
--         simp at h g₀
--         tauto
--         -- we could define exact ![1,0,1,1,1,0,1] but we want undefined
--       ·
--         have : σ.1 = ![1,1] := by
--           ext l
--           fin_cases l
--           simp_all
--           sorry
--           sorry
--         rw [this] at *
--         have h := σ.2
--         unfold lensDomain focalLen x at h
--         simp at h g₀
--         tauto
--     have h := σ.2
--     unfold lensDomain at h
--     simp at h
--     sorry -- too many cases


/-- need the kind of extension where
we can switch from `z` to `x` and, because there are fewer focal points
(the ones where `z` and `x` differ being removed),
`z` remains in the domain.
-/
def switchto {s : ℕ} (z x : Fin s → Fin 2)  (focLen : Set (Fin s.succ)) :=
  lensDomain x {i : (Fin s.succ) | i ∈ focLen
    ∧ ∀ j, (h : j < i) → x ⟨j.1,by omega⟩
             = z ⟨j.1,by omega⟩
  }


theorem xlensDomain {s : ℕ} (_ x : Fin s → Fin 2)  (focLen : Set (Fin s.succ)):
    x ∈ lensDomain x focLen _ := by
  unfold lensDomain
  intro f _ h j
  rfl


theorem zinswitchto {s : ℕ} (z x : Fin s → Fin 2)  (focLen : Set (Fin s.succ)):
    z ∈ switchto z x focLen _ := fun f g h j => by
  have := g.2 ⟨j.1, by omega⟩ j.2
  symm
  exact this

theorem subset_switchto {s l : ℕ} (z x : Fin s → Fin 2)  (focLen : Set (Fin s.succ)):
    lensDomain x focLen l ⊆ switchto z x focLen l := by
  intro σ hσ
  simp [switchto, lensDomain] at hσ ⊢
  intro f hf hxz h j
  specialize hxz ⟨j.1, by omega⟩ j.2
  specialize hσ f hf h j
  simp_all only

theorem xinswitchto {s : ℕ} (z x : Fin s → Fin 2)  (focLen : Set (Fin s.succ)):
    x ∈ switchto z x focLen _ := by
  apply subset_switchto
  intro f _ h j
  rfl


theorem lensDomain₁ : lensDomain x focalLen _ ![] := by
  intro f _ h
  simp at h

theorem lensDomain₀ {b : Fin 2} : lensDomain x focalLen _ ![b] := by
  intro i _ h
  unfold x
  simp at h
  intro j
  have := j.2
  omega
theorem lensDomain₁₂ {b : Fin 2} : lensDomain x focalLen _ ![0,b] := by
  intro f g h
  simp at h
  unfold focalLen at g
  have : f.1 = 0 ∨ f.1 = 1 := by omega
  cases this with
  | inl h =>
    intro j
    have := j.2
    omega
  | inr h =>
    intro j
    have := j.2
    have : j.1 = 0 := by omega
    simp_rw [this]
    unfold x
    rfl
theorem lensDomain₃ {b : Fin 2} : ¬ lensDomain x focalLen _ ![1,b] := by
  intro hc
  unfold lensDomain x at hc
  specialize hc 1 (by unfold focalLen;simp) (by aesop) ⟨0,by aesop⟩
  simp at hc

theorem lensDomain₄ {b : Fin 2} : ¬ lensDomain x focalLen _ ![0,0,b] := by
  intro hc
  unfold lensDomain x at hc
  specialize hc 2 (by unfold focalLen;simp) (by aesop) ⟨1,by aesop⟩
  simp at hc



-- /-- σ extends x up to the last focalLength below |σ| -/
-- def lensDomainain {l : Fin 6} (σ : Fin l.1 → Fin 2) : Prop :=
--   ∀ i : Fin 5, (g : (focalLength i).1 < l.1) →
--     ∀ j : Fin (focalLength i).1, σ ⟨j.1, by omega⟩ -- (Fin.castLT j (by omega)) --⟨j.1, by omega⟩
--       = x ⟨j.1, by omega⟩ -- (Fin.castLT j (by omega))

-- theorem ind : lensDomainain (l := 0) ![] := by
--   unfold lensDomainain
--   intro i g
--   simp at g

-- theorem xlensDomainain : lensDomainain (l := 5) x := fun _ _ _ => rfl
-- theorem anotherlensDomainain' : ¬ lensDomainain (l := 2) ![1,0] := fun hc => by
--   unfold lensDomainain at hc
--   specialize hc 1
--     (by unfold focalLength;simp)
--     (by unfold focalLength;simp;exact 0)
--   simp at hc
--   unfold x at hc
--   simp at hc

-- theorem anotherlensDomainain'' : lensDomainain (l := 1) ![1] := by
--   intro i g j
--   simp at g
--   have := j.2
--   omega

-- theorem anotherlensDomainain : lensDomainain (l := 2) ![0,1] := by
--   intro i g j
--   unfold x
--   unfold focalLength at *
--   fin_cases i
--   · have := j.2
--     simp at this
--   · have := j.2
--     conv at this =>
--       right
--       change 1
--     have : ![(0 : Fin 2), 1, 1, 0, 1] = Fin.append ![0,1] ![1,0,1] := by
--       ext k
--       fin_cases k <;> aesop
--     have : ![(0 : Fin 2), 1, 1, 0, 1] ⟨↑j, by omega⟩ =
--            ![0, 1] ⟨↑j, by omega⟩ := by
--       rw [this]
--       simp [Fin.append, Fin.addCases]
--       rfl
--     rw [this]
--   · conv at g =>
--       lhs
--       change 2
--     simp at g
--   · conv at g =>
--       lhs
--       change 4
--     simp at g
--   · conv at g =>
--       lhs
--       change 5
--     simp at g
