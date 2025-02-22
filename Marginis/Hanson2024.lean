import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!

# Some semilattices of definable sets in continuous logic

[JAMES E. HANSON](http://logicandanalysis.org/index.php/jla/article/view/493)

Definition 1.1 defines a topometric space.

In the ordering of topologies, ⊥ is the discrete topology and τ₀ ≤ τ₁ means
τ₀ refines τ₁, i.e., τ₀ ⊇ τ₁.

Note that neither the trivial ⊤ or discrete ⊥ topology can be paired with the
usual metric on ℝ to form a topometric space; so the notion is subtle.
We merely prove that if we use the same topology as that obtained from the metric
then we always have a topometric space.
-/

/-- Topometric space structure on `X`. -/
class TopometricSpace (X : Type) where
  topology : TopologicalSpace X
  metric : MetricSpace X
  refines : metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace ≤ topology
  lowerSemiContinuous (ε : Set.Ioi (0:ℝ)) :
    @IsClosed (Fin 2 → X)
      (@Pi.topologicalSpace (Fin 2) (fun _ => X) (fun _ => topology))
      {v | metric.dist (v 0) (v 1) ≤ ε }

/-- If we in particular let the topology be that obtained from the metric
then we do have a topometric space. -/
def EasyTopometric (X : Type) [m : MetricSpace X] : TopometricSpace X := {
  metric := m
  topology := m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  refines := by simp
  lowerSemiContinuous := fun ε =>
    isClosed_le (Continuous.dist (continuous_apply 0) (continuous_apply 1)) continuous_const
}
