import Mathlib.Order.Basic
import Mathlib.Tactic

/-!

## Convergence in formal topology: a unifying notion
FRANCESCO CIRAULO
MARIA EMILIA MAIETTI
GIOVANNI SAMBIN

The article discusses distributivity in various senses.
Here we consider left-distributivity and its relationship with idempotency.

Over `Fin 0` and `Fin 1` every function is both left-distributive and idempotent.
Over `Fin 2` (or `Bool`), idempotency implies left-distributivity but not the other way
around, and there are functions that are neither.

The idempotents on `Bool` are exactly AND, OR, π₁, π₂.

Over `Fin 3` there exist functions that are idempotent and not
left-distributive. (In fact, it is the norm rather than the exception.)

We also prove some properties of Laver tables.

-/

def idempotent {U : Type*} (f : U → U → U) :=
  ∀ x, f x x = x

def leftdistributive {U : Type*} (f : U → U → U) :=
  ∀ a b c, f a (f b c) = f (f a b) (f a c)

theorem nil_leftdistributive_idempotent (f : Fin 0 → Fin 0 → Fin 0) :
    leftdistributive f ∧ idempotent f := by
  constructor <;> (
  intro z
  have := z.2
  simp at this)

theorem one_leftdistributive_idempotent (f : Fin 1 → Fin 1 → Fin 1) :
  leftdistributive f ∧ idempotent f := by
  constructor <;> (intro a; aesop)

theorem two_neither_leftdistributive_idempotent :
    ∃ f : Fin 2 → Fin 2 → Fin 2, ¬ leftdistributive f ∧ ¬ idempotent f := by
  use fun x y => x + y
  constructor
  · intro hc
    specialize hc 1 1 1
    simp at hc
  · intro hc
    specialize hc 1
    simp at hc

theorem bool_neither_leftdistributive_idempotent :
    ∃ f : Bool → Bool → Bool, ¬ leftdistributive f ∧ ¬ idempotent f := by
  use xor
  constructor
  · intro hc
    specialize hc true true true
    simp at hc
  · intro hc
    specialize hc true
    simp at hc

/-- The only idempotents on `Bool` and AND, OR, π₁ and π₂. -/
theorem the_four_idempotents (f : Bool → Bool → Bool)
  (hf : idempotent f) :
  ((f = fun p _ : Bool => p)
  ∨ (f = fun p q => q)
  ∨ (f = fun p q : Bool => ((p ∧ q) : Bool))
  ∨ (f = fun p q : Bool => ((p ∨ q) : Bool))) := by
  have h₀ : f false true = false ∨ f false true = true := by aesop
  have h₁ : f true false = false ∨ f true false = true := by aesop
  cases h₀ with
  | inl h =>
    cases h₁ with
    | inl g =>
      right
      right
      left
      ext b c
      cases b
      cases c
      · simp
        apply hf
      · simp
        apply h
      simp
      cases c
      · apply g
      · apply hf
    | inr g =>
      left
      ext b c
      cases b
      cases c
      · apply hf
      · apply h
      cases c
      · apply g
      · apply hf
  | inr h =>
    cases h₁ with
    | inl g =>
      right
      left
      ext a b
      cases a
      cases b
      apply hf
      apply h
      cases b
      apply g
      apply hf
    | inr g =>
      right
      right
      right
      ext a b
      cases a
      cases b
      simp
      apply hf
      simp
      apply h
      simp
      cases b
      apply g
      apply hf

theorem characterize_idempotents (f : Bool → Bool → Bool) :
  idempotent f ↔
  ((f = fun p _ : Bool => p)
  ∨ (f = fun p q => q)
  ∨ (f = fun p q : Bool => ((p ∧ q) : Bool))
  ∨ (f = fun p q : Bool => ((p ∨ q) : Bool))) := by
  constructor
  · apply the_four_idempotents
  intro h
  unfold idempotent
  cases h with
  | inl h =>
    subst h
    simp
  | inr h =>
    cases h with
    | inl h =>
      subst h
      simp
    | inr h =>
      cases h with
      | inl h =>
      subst h
      simp
      | inr h =>
      subst h
      simp


/-- Most idempotents are not left-distributive. Indeed, if we impose
idempotency we are free to assign values to all off-diagonal inputs. -/
theorem three_exists_idempotent_not_leftdistributive :
    ∃ f : Fin 3 → Fin 3 → Fin 3, idempotent f ∧ ¬ leftdistributive f := by
  use fun x y => ite (x = y) x ( ite (x = 2 ∨ y = 2) (x + y) 2)
  constructor
  · intro a
    simp
  · intro hc
    unfold leftdistributive at hc
    let f := fun x y : Fin 3 => ite (x = y) x ( ite (x = 2 ∨ y = 2) (x + y) 2)
    conv at hc =>
      change ∀ a b c, f a (f b c) = f (f a b) (f a c)
    specialize hc 0 1 2
    simp [f] at hc


/-- The idea is that if f is idempotent then f(false,false)=false and f(true,true)=true
  so there only 4 possibilities:
  1. f(F,T)=f(T,F)=F: this is logical AND
  2. f(F,T)=f(T,F)=T: this is logical OR
  3. f(F,T)=T, f(T,F)=F: this is "q"
  4. f(F,T)=F, f(T,F)=T: this is "p"
-/
theorem leftdistributive_of_idempotent_bool (f : Bool → Bool → Bool)
  (hf : idempotent f) : leftdistributive f := by
  intro a b c
  cases the_four_idempotents f hf with
  | inl h =>
    subst h
    simp
  | inr h =>
    cases h with
    | inl h =>
      subst h
      simp
    | inr h =>
      cases h with
      | inl h =>
        subst h
        simp
        cases a <;> (cases b <;> cases c <;> simp)
      | inr h =>
        subst h
        simp
        cases a <;> (cases b <;> cases c <;> simp)

theorem exists_leftdistributive_not_idempotent_bool :
    ∃ f : Bool → Bool → Bool, leftdistributive f ∧ ¬ idempotent f := by
  use fun p q => p → q
  constructor
  · intro a b c
    simp
    cases a
    cases b
    cases c
    simp
    rfl
    rfl
    rfl
  · intro hc
    specialize hc false
    simp at hc

def laver {n : ℕ} (f : Fin (2^n) → Fin (2^n) → Fin (2^n)) :=
  ∀ k, f k 1 = k + 1

theorem laver₀ : ∃! f : Fin (2^0) → Fin (2^0) → Fin (2^0), laver f ∧ leftdistributive f := by
  use fun _ _ => 0
  constructor
  · constructor
    · intro k
      simp
      aesop
    · intro _ _ _
      simp
  intro f _
  ext x y
  simp


lemma help_deduce_laver {n : ℕ} {f : Fin (2^n) → Fin (2^n) → Fin (2^n)}
    (hf₀ : laver f) (x y : Fin (2^n)):
    f x y = f x (f (y-1) 1) := by
  have := hf₀ (y-1)
  rw [this]
  simp


theorem deduce_laver₀₂ {m : ℕ} {f : Fin (2^(m)) → Fin (2^m) → Fin (2^m)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 0 2 = 2 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  have : 2 - (1 : Fin (2^m)) = 1 := by
    have := @eq_sub_of_add_eq' (Fin (2^(m))) _ 1 2 1
        (by exact one_add_one_eq_two)
    rw [← this]
  rw [this]
  rw [hf₀,hf₀]
  simp
  exact one_add_one_eq_two

theorem deduce_laver₀₃ {m : ℕ} {f : Fin (2^(m)) → Fin (2^m) → Fin (2^m)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 0 3 = 3 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  have : 3 - (1 : Fin (2^m)) = 2 := by
    have := @eq_sub_of_add_eq' (Fin (2^(m))) _ 2 3 1
        (by rw [add_comm];exact two_add_one_eq_three)
    rw [← this]
  rw [this]
  rw [deduce_laver₀₂ hf₀ hf₁]
  rw [hf₀]
  exact two_add_one_eq_three

theorem laver₁ : ∃! f : Fin (2^1) → Fin (2^1) → Fin (2^1), laver f ∧ leftdistributive f := by
  use !![0,1; 0,0]
  constructor
  · simp
    constructor
    · intro k
      fin_cases k <;> simp
    · intro a b c
      fin_cases a <;> (fin_cases b <;> (fin_cases c <;> simp))
  · intro f hf
    have hf₀ := hf.1
    have hf₁ := hf.2
    have h₀ := hf₀ 0
    have h₁ := hf₀ 1
    simp at h₀ h₁
    ext x y
    fin_cases x
    · fin_cases y
      · simp
        have h₀₁₁ := hf₁ 0 1 1
        rw [h₀, h₁] at h₀₁₁
        rw [h₀₁₁]
        rfl
      · simp
        rw [hf.1 0]
        rfl
    · fin_cases y
      · have : (f 1 0).1 = 0 ∨ (f 1 0).1 = 1 := by omega
        cases this with
        | inl h => exact h
        | inr h =>
        have h₀₁₁ := hf₁ 0 1 1
        have h₁₁₁ := hf₁ 1 1 1
        simp_all
      · simp_all [hf.1 1]


theorem deduce_laver₀₀ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 0 0 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [hf₀]
  rw [show (-1 : Fin (2^2)) = 3 by rfl]
  rw [deduce_laver₀₃ hf₀ hf₁]
  simp

theorem deduce_laver₃₂ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 3 2 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [hf₀]
  apply deduce_laver₀₀ hf₀ hf₁

theorem deduce_laver₃₃ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 3 3 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [deduce_laver₃₂ hf₀ hf₁, deduce_laver₀₀ hf₀ hf₁]

theorem deduce_laver₃₀ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 3 0 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [show (-1 : Fin (2^2)) = 3 by rfl]
  rw [deduce_laver₃₃ hf₀ hf₁, deduce_laver₀₀ hf₀ hf₁]

theorem deduce_laver₂₂ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 2 2 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [hf₀]
  simp
  rw [deduce_laver₃₃ hf₀ hf₁]

theorem deduce_laver₂₃ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 2 3 = 3 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [deduce_laver₂₂ hf₀ hf₁, deduce_laver₀₃ hf₀ hf₁]

theorem deduce_laver₂₀ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 2 0 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [show (-1 : Fin (2^2)) = 3 by rfl]
  rw [deduce_laver₂₃ hf₀ hf₁, deduce_laver₃₃ hf₀ hf₁]

theorem deduce_laver₁₂ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 1 2 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [hf₀]
  simp
  rw [deduce_laver₂₂ hf₀ hf₁]

theorem deduce_laver₁₃ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 1 3 = 2 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [deduce_laver₁₂ hf₀ hf₁, deduce_laver₀₂ hf₀ hf₁]

theorem deduce_laver₁₀ {f : Fin (2^2) → Fin (2^2) → Fin (2^2)}
    (hf₀ : laver f) (hf₁ : leftdistributive f) :
    f 1 0 = 0 := by
  rw [help_deduce_laver hf₀, hf₁, hf₀]
  simp
  rw [show (-1 : Fin (2^2)) = 3 by rfl]
  rw [deduce_laver₁₃ hf₀ hf₁, deduce_laver₂₂ hf₀ hf₁]


def mylaver₂ : Fin (2^2) → Fin (2^2) → Fin (2^2) := !![
    0,1,2,3;
    0,2,0,2;
    0,3,0,3;
    0,0,0,0]

def mylaver₃ : Fin (2^3) → Fin (2^3) → Fin (2^3) := !![
    0, 1, 2, 3, 4, 5, 6, 7;
    0, 2, 4, 6, 0, 2, 4, 6;
    0, 3, 4, 7, 0, 3, 4, 7;
    0, 4, 0, 4, 0, 4, 0, 4;
    0, 5, 6, 7, 0, 5, 6, 7;
    0, 6, 0, 6, 0, 6, 0, 6;
    0, 7, 0, 7, 0, 7, 0, 7;
    0, 0, 0, 0, 0, 0, 0, 0]

theorem laver₃ : ∃ f : Fin (2^3) → Fin (2^3) → Fin (2^3), laver f := by
  use mylaver₃
  unfold mylaver₃
  intro x
  fin_cases x <;> rfl

theorem laver₂ : ∃! f : Fin (2^2) → Fin (2^2) → Fin (2^2), laver f ∧ leftdistributive f := by
  use mylaver₂
  unfold mylaver₂
  constructor
  · constructor
    · intro x
      fin_cases x <;> rfl
    · intro a b c
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
  intro f hf
  have hf₀ := hf.1
  have hf₁ := hf.2
  ext x y
  fin_cases x
  · have h₀₀ := deduce_laver₀₀ hf₀ hf₁
    have := hf₀ 0
    have h₀₂ := deduce_laver₀₂ hf₀ hf₁
    have h₀₃ := deduce_laver₀₃ hf₀
    fin_cases y <;> simp_all
  · have h₁₀ := deduce_laver₁₀ hf₀ hf₁
    have := hf₀ 1
    have h₁₂ := deduce_laver₁₂ hf₀ hf₁
    have h₁₃ := deduce_laver₁₃ hf₀ hf₁
    fin_cases y <;> simp_all
  · have h₂₀ := deduce_laver₂₀ hf₀ hf₁
    have := hf₀ 2
    have h₂₂ := deduce_laver₂₂ hf₀ hf₁
    have h₂₃ := deduce_laver₂₃ hf₀ hf₁
    fin_cases y <;> (simp_all; try rfl)
  · have h₃₀ := deduce_laver₃₀ hf₀ hf₁
    have := hf₀ 3
    have h₃₂ := deduce_laver₃₂ hf₀ hf₁
    have h₃₃ := deduce_laver₃₃ hf₀ hf₁
    fin_cases y <;> (simp_all; try rfl)

/-- See https://www.maths.tcd.ie/~lebed/Lebed_ATS14.pdf -/
def color_propagation (f : Fin (2^2) → Fin (2^2) → Fin (2^2)) :
    (Fin (2^2) × Fin (2^2)) → (Fin (2^2) × Fin (2^2)) := by
  intro (a,b)
  exact (f a b, a)

theorem color_propagation_invertible : ¬ Function.Injective (color_propagation mylaver₂) := by
  intro hc
  specialize hc (by
    show color_propagation mylaver₂ (1,0) = color_propagation mylaver₂ (1,2)
    unfold color_propagation mylaver₂
    simp)
  simp at hc
