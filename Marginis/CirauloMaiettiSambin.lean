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
