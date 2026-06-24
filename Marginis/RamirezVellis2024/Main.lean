/-
Copyright (c) 2026 Austin Anderson and Tony Ou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson, Tony Ou
AnalysTSP.lean done without AI
Other files assisted by AI: Gemini and Claude
-/

import Mathlib
import Marginis.RamirezVellis2024.AnalysTSP
import Marginis.RamirezVellis2024.WeierstrassLimitR2
import Marginis.RamirezVellis2024.AnalyticTSP
import Marginis.RamirezVellis2024.HausdorffVariation

open AnalyticTSP
open ManualEuclideanR2

/-!
# Countable bounded set with no rectifiable path cover
From page 2 in paper: "For example, if
V is the set of all points in the unit square [0,1]^2
with rational coordinates, it is not hard to see that V
is bounded and countable but there exists no rectifiable curve that contains V"

Our formalizastion shows there exists no rectifiable path
covering ℚ×ℚ ∩ [0,1]×[0,1] in the plane, as an example
of a bounded countable set for which no solution to the
analyst's travelling salesman problem exists. We build
countability of the set from elementary principles and use a
compactness argument.
-/

theorem Main_ATSP_Failure :
  ¬ ∃ (S : Set (ℝ × ℝ)) (L : ℝ), IsPathInR2 S ∧ CtsRectifiable S L ∧ UnitRationalSquare ⊆ S := by {
  exact ATSP_Rational_Failure
}

/-!
## Glossary of Custom Definitions

The theorem statement `Main_ATSP_Failure` uses three project-specific
definitions. Their full meaning is expanded below so the theorem can be
read without chasing imports.

### `IsPathInR2 S`  (defined in `WeierstrassLimitR2.lean`)

A set `S ⊆ ℝ × ℝ` is a **path** when there exists a continuous surjection
from the unit interval onto `S`:

```
def IsPathInR2 (S : Set (ℝ × ℝ)) : Prop :=
  ∃ φ : (UnitInterval → S), Function.Surjective φ ∧ IsCtsRtoR2 φ
```

The sub-definitions are:

- **`UnitInterval`** = `{ r : ℝ | 0 ≤ r ∧ r ≤ 1 }`, the closed interval [0, 1].

- **`IsCtsRtoR2 φ`** = `∀ x, LimitSubsetsRtoR2' φ x (f x)`, i.e. `φ` is
  continuous at every point of its domain, where continuity uses the
  project's manual ε-δ definition against the custom Euclidean distance.

- **`LimitSubsetsRtoR2' f a L`** =
  `∀ ε > 0, ∃ δ > 0, ∀ x, dist x a < δ ∧ x ≠ a → euclideanDist (f x) L < ε`,
  i.e. the standard epsilon-delta limit for maps from subsets of ℝ into
  subsets of ℝ × ℝ, using Lean's built-in `dist` on ℝ and the project's
  hand-rolled `euclideanDist` on ℝ × ℝ.

- **`euclideanDist x y`** = `√((x.1 - y.1)² + (x.2 - y.2)²)`,
  the standard Euclidean distance in the plane, defined manually to keep
  the compactness proofs self-contained without relying on Mathlib's
  `MetricSpace` instance for the core argument.

### `CtsRectifiable S L`  (defined in `AnalyticTSP.lean`)

A set `S ⊆ ℝ × ℝ` is **rectifiable with length bound `L`** when there is
a continuous parameterization whose partition sums never exceed `L`:

```
def CtsRectifiable (S : Set (ℝ × ℝ)) (L : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ × ℝ, Continuous φ ∧ (S ⊆ φ '' Icc 0 1) ∧
    ∀ (N : ℕ) (t : Fin N → ℝ), IsPartitionR N t → PathVariation φ N t ≤ L
```

The sub-definitions are:

- **`IsPartitionR N t`** =
  `(∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ (∀ i j, i ≤ j → t i ≤ t j)`,
  i.e. `t` is an ordered sequence of `N` points in [0, 1].

- **`PathVariation φ N t`** =
  `∑ i : Fin (N-1), euclideanDist (φ (t i)) (φ (t (i+1)))`,
  the total length of the polygonal approximation obtained by connecting
  successive images `φ(t₀), φ(t₁), …, φ(t_{N-1})`.

### `UnitRationalSquare`  (defined in `AnalyticTSP.lean`)

The set of all rational-coordinate points in the closed unit square:

```
def UnitRationalSquare : Set (ℝ × ℝ) :=
  { p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧
        ∃ (q1 q2 : ℚ), (q1 : ℝ) = p.1 ∧ (q2 : ℝ) = p.2 }
```

This is ℚ × ℚ ∩ [0,1]², the bounded dense countable subset of the plane
whose non-rectifiability we establish.

### Proof outline

The proof (`ATSP_Rational_Failure` in `AnalyticTSP.lean`) proceeds by
contradiction in four steps:

1. **Density**: `UnitRationalSquare` is dense in `[0,1]²`, so if `S`
   contains the rational square, then `closure S ⊇ [0,1]²`.

2. **Compactness**: `IsPathInR2 S` implies `S` is compact (the continuous
   image of the compact interval `[0,1]`), proved in
   `PathsCompact` via the manually verified Bolzano-Weierstrass theorem.

3. **Closed + dense ⇒ contains the solid square**: A compact subset of ℝ²
   is closed, so `S = closure S ⊇ [0,1]²`.

4. **Dimension contradiction**: The 2-dimensional Hausdorff measure
   `μH[2]` of the unit square is positive, but `CtsRectifiable S L`
   forces `μH[2] S = 0` because rectifiable curves are 1-dimensional.
   This contradicts `[0,1]² ⊆ S`.
-/
