import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Defs

-- lattice tables...

structure latticeTable (A : Type*) where
  (Θ : Set <| A → A → Prop)
  (h : (fun _ _ => True) ∈ Θ ∧
       (fun x y => x=y) ∈ Θ ∧
    (∀ α ∈ Θ, ∀ β ∈ Θ, (fun x y => α x y ∧ β x y) ∈ Θ) ∧
    (∀ α ∈ Θ, ∀ β ∈ Θ, Relation.Join (Relation.ReflTransGen  (fun x y => α x y ∨ β x y)) ∈ Θ) ∧ -- need eq. closure
    ∀ α ∈ Θ, IsEquiv _ α)


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
                        refine Relation.reflTransGen_eq_self (congrFun rfl) ?trans
                        exact transitive_of_trans fun x y ↦ x = y
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
                  ⟨c₀, ⟨hc₀.1, hc₁.2.trans <| (hc₁.1.symmetric hs).trans hc₀.2⟩⟩
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
    push_neg at h ⊢
    ext x
    aesop


lemma not_id_or_const {A : Type*} {f : A → A} (hf₀ : f ≠ id) (hf₁ : ∀ c, f ≠ fun _ => c) :
  ∃ a b, a ≠ f a ∧ f a ≠ f b := by
    rw [← const_iff] at hf₁
    obtain ⟨a,ha⟩ : ∃ a, f a ≠ a := by
      contrapose hf₀
      push_neg at hf₀ ⊢
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
  push_neg at h ⊢
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
        push_neg at this ⊢
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
      push_neg at H
      simp at H
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

/-
                (Infinite case)         (Finite case)

EndPart = clone ()
        = pp    (`pp_eq_clone_of_inf`)



-/
