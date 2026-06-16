import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.GroupTheory.PushoutI
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Sketches for arithmetic universes
STEVEN VICKERS

The article discusses pushouts. Here we construct a version of pushouts by hand.
-/


def pushout {U V W : Type*} (f : U → V) (g : U → W)
  (hf : Function.Injective f)
  (hg : Function.Injective g) : Setoid (V ⊕ W) := by
  exact {
    r := fun x y => by
      cases x with
      | inl v =>
        cases y with
        | inl v' => exact v = v'
        | inr w => exact ∃ u, f u = v ∧ g u = w
      | inr w =>
        cases y with
        | inl v => exact ∃ u, f u = v ∧ g u = w
        | inr w' => exact w = w'
    iseqv := {
      refl := fun x => by cases x <;> simp
      symm := by
        intro x y h
        cases x with
        | inl val =>
          cases y with
          | inl v => simp;simp at h;tauto
          | inr v => simp;simp at h;tauto
        | inr val =>
          cases y with
          | inl v => simp;simp at h;tauto
          | inr v => simp;simp at h;tauto
      trans := by
        intro x y z h₀ h₁
        cases x with
        | inl v =>
          cases y with
          | inl v =>
            cases z with
            | inl v' => simp;simp at h₀ h₁;aesop
            | inr v' => simp;simp at h₀ h₁;aesop
          | inr w =>
            cases z with
            | inl v' =>
              simp;simp at h₀ h₁
              obtain ⟨u₀,hu₀⟩ := h₀
              obtain ⟨u₁,hu₁⟩ := h₁
              have : u₀ = u₁ := by apply hg;aesop
              subst this
              apply hu₀.1.symm.trans
              tauto
            | inr v' =>
              simp;simp at h₀ h₁
              subst h₁
              obtain ⟨u₀,hu₀⟩ := h₀
              use u₀
        | inr w =>
          cases y with
          | inl v =>
            cases z with
            | inl v' =>
              simp;simp at h₀ h₁
              subst h₁
              obtain ⟨u₀,hu₀⟩ := h₀
              use u₀
            | inr w' =>
              simp;simp at h₀ h₁
              obtain ⟨u₀,hu₀⟩ := h₀
              obtain ⟨u₁,hu1⟩ := h₁
              have : u₀ = u₁ := by apply hf;aesop
              subst this
              apply hu₀.2.symm.trans
              tauto
          | inr v =>
            cases z with
            | inl val =>
              simp;simp at h₀ h₁
              subst h₀
              obtain ⟨u₁,hu₁⟩ := h₁
              use u₁
            | inr val =>
              simp;simp at h₀ h₁
              subst h₀
              obtain ⟨u₁,hu₁⟩ := h₁
              rfl
    }
  }


/-- A model for the linear logic ⅋ connective.
This is only the ambient space though.
-/
@[reducible]
def ambient⅋ (V W : Type*) [Zero V] [Zero W] := @pushout (Fin 2) (Fin 2 × V) (Fin 2 × W)
    (fun i : Fin 2 => ((i,0) : Fin 2 × V))
    (fun i : Fin 2 => ((i,0) : Fin 2 × W))
    (by intro x;simp) (by intro x;simp)
open Sum

/-- The ⅋ for propositions A, B. -/
def ⅋' {V W : Type*} [Zero V] [Zero W] (𝓐 : Set V) (𝓑 : Set W) : Set (Quotient (ambient⅋ V W)) := by
  intro c
  exact (∃ C, (c = ⟦ inl C ⟧ ∧ 𝓐 C.2))
      ∨ (∃ C, (c = ⟦ inr C ⟧ ∧ 𝓑 C.2))



def opl {V W : Type*} [Zero V] [Zero W] (𝓐 : Set V) (𝓑 : Set W) : Set (Quotient (ambient⅋ V W)) := by
  intro c
  exact (∃ C, (c = ⟦ inl C ⟧ ∧ 𝓐 C.2 ∧ C.1 = 0))
      ∨ (∃ C, (c = ⟦ inr C ⟧ ∧ 𝓑 C.2 ∧ C.1 = 0))

instance {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  (𝓐 : Submodule 𝕜 E) :
  Zero 𝓐 := 𝓐.zero


/-- `𝓐 ⊕ 𝓑` implies `𝓐 ⅋ 𝓑`. -/
theorem ⅋_of_opl  {V W : Type*} [Zero V] [Zero W] (𝓐 : Set V) (𝓑 : Set W) :
  ∀ C, opl 𝓐 𝓑 C → ⅋' 𝓐 𝓑 C := by
  intro C h
  unfold opl at h
  unfold ⅋'
  aesop




open Sum in
example : Unit := by
  let p := @pushout (Fin 2) (Fin 2 × Fin 2) (Fin 2 × Fin 2)
    (fun i : Fin 2 => ((i,0) : Fin 2 × Fin 2))
    (fun i : Fin 2 => ((i,0) : Fin 2 × Fin 2))
    (by intro x;simp) (by intro x;simp)

  have : ¬ p.r (inl (0,1)) (inr (0,0)) := by sorry --simp[Setoid.r, p, pushout]
  have : ¬ p.r (inl (1,0)) (inr (0,0)) := by sorry --simp[Setoid.r, p, pushout]
  have : ¬ p.r (inl (1,1)) (inr (0,0)) := by sorry --simp[Setoid.r, p, pushout]

  have : ¬ p.r (inl (0,0)) (inr (1,0)) := by sorry --simp[Setoid.r, p, pushout]
  have : ¬ p.r (inl (0,1)) (inr (1,0)) := by sorry --simp[Setoid.r, p, pushout]
  have : ¬ p.r (inl (1,1)) (inr (1,0)) := by sorry --simp[Setoid.r, p, pushout]

  have H₁ (a : Fin 2) :       p.r (inl (a,0)) (inr (a,0)) := by sorry --simp[Setoid.r, p, pushout]
  have (a b c : Fin 2) : ¬ p.r (inl (a,b)) (inr (c,1)) := by sorry --simp[Setoid.r, p, pushout]
  have : ∀ z,
      p.r z (inl (0,0))
    ∨ p.r z (inl (0,1))
    ∨ p.r z (inl (1,0))
    ∨ p.r z (inl (1,1))
    ∨ p.r z (inr (0,1))
    ∨ p.r z (inr (1,1)) := by
    intro z
    cases z with
    | inl val =>
      have : val.1 = 0 ∨ val.1 = 1 := by omega
      cases this with
      | inl h₁ =>
        have : val.2 = 0 ∨ val.2 = 1 := by omega
        cases this with
        | inl h₂ =>
          left
          have : val = (0,0) := by aesop
          rw [this]
        | inr h₂ =>
          right
          left
          have : val = (0,1) := by aesop
          rw [this]
      | inr h =>
        have : val.2 = 0 ∨ val.2 = 1 := by omega
        cases this with
        | inl h₂ =>
          right
          right
          left
          have : val = (1,0) := by aesop
          rw [this]
        | inr h₂ =>
          right
          right
          right
          left
          have : val = (1,1) := by aesop
          rw [this]
    | inr val =>
      have : val.1 = 0 ∨ val.1 = 1 := by omega
      cases this with
      | inl h₁ =>
        have : val.2 = 0 ∨ val.2 = 1 := by omega
        cases this with
        | inl h₂ =>
          left
          have : val = (0,0) := by aesop
          rw [this]
          exact H₁ 0
        | inr h₂ =>
          right
          right
          right
          right
          left
          have : val = (0,1) := by aesop
          rw [this]
      | inr h =>
        have : val.2 = 0 ∨ val.2 = 1 := by omega
        cases this with
        | inl h₂ =>
          right
          right
          left
          have : val = (1,0) := by aesop
          rw [this]
          exact H₁ 1
        | inr h₂ =>
          right
          right
          right
          right
          right
          have : val = (1,1) := by aesop
          rw [this]
  exact Unit.unit
/-
Comprehensive list of points
inl (0,0) = inr (0,0)
inl (0,1)
inl (1,0) = inr (1,0)
inl (1,1)
inr (0,1)
inr (1,1)
-/
