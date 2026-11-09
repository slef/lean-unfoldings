module

public import Unfoldings.Path.Reparameterization
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Shortest paths in compact metric spaces

Any two points joined by a rectifiable path in a compact metric space admit a
length-minimizing path. This compares against all continuous paths, with no
speed assumption on competitors. The minimizing path can be chosen with speed
bounded by its own length.

The bounded-speed compactness argument adapts `SurfacePathCompactness.lean`
and `ShortestSurfacePaths.lean` in slef/EdgeUnfoldings, snapshot
56caca8cdc44dbc2f839e93808088d56ea3f0780, generalized to arbitrary compact
metric spaces without any polyhedron or surface premise.
-/

@[expose] public section

open Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology

namespace Path

variable {X : Type*} [MetricSpace X]

/-- A closed family of curves with fixed endpoints and a common speed bound. -/
def boundedSpeedCurves (a b : X) (K : ℝ≥0) : Set (unitInterval →ᵇ X) :=
  {f | f 0 = a ∧ f 1 = b ∧ LipschitzWith K f}

theorem boundedSpeedCurves_closed (a b : X) (K : ℝ≥0) : IsClosed (boundedSpeedCurves a b K) := by
  have evaluation (t : unitInterval) : Continuous (fun f : unitInterval →ᵇ X => f t) :=
    continuous_eval_const t
  have speeds : IsClosed {f : unitInterval →ᵇ X | LipschitzWith K f} := by
    simp only [LipschitzWith, ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_le ((evaluation x).edist (evaluation y)) continuous_const))
  exact (isClosed_eq (evaluation 0) continuous_const).inter
    ((isClosed_eq (evaluation 1) continuous_const).inter speeds)

theorem curve_eLength_lowerSemicontinuous :
    LowerSemicontinuous (fun f : unitInterval →ᵇ X => eVariationOn f Set.univ) := by
  intro f length smaller
  exact eVariationOn.lowerSemicontinuous_aux
    (fun t _ => (continuous_eval_const t).tendsto f) smaller

variable [CompactSpace X]

theorem boundedSpeedCurves_compact (a b : X) (K : ℝ≥0) : IsCompact (boundedSpeedCurves a b K) := by
  apply BoundedContinuousFunction.arzela_ascoli₂ Set.univ isCompact_univ _
    (boundedSpeedCurves_closed a b K) (fun _ _ _ => Set.mem_univ _)
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => K * r)
    (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
  intro x y f
  exact f.property.2.2.dist_le_mul x y

theorem boundedSpeedCurves_minimum (a b : X) (K : ℝ≥0)
    (nonempty : (boundedSpeedCurves a b K).Nonempty) :
    ∃ f ∈ boundedSpeedCurves a b K, ∀ g ∈ boundedSpeedCurves a b K,
      eVariationOn f Set.univ ≤ eVariationOn g Set.univ :=
  (curve_eLength_lowerSemicontinuous.lowerSemicontinuousOn _).exists_isMinOn nonempty
    (boundedSpeedCurves_compact a b K)

/-- A rectifiable path in a compact metric space can be replaced by a shortest path. -/
theorem exists_lengthMinimizing {a b : X} (p : Path a b) (finite : p.eLength ≠ ⊤) :
    ∃ q : Path a b, q.IsLengthMinimizing ∧ q.eLength ≠ ⊤ := by
  obtain ⟨fast, speed, _, _⟩ := p.exists_lipschitz_reparameterization finite
  let K := p.eLength.toNNReal
  let first : unitInterval →ᵇ X := mkOfCompact fast.toContinuousMap
  have first_in : first ∈ boundedSpeedCurves a b K := ⟨fast.source, fast.target, speed⟩
  obtain ⟨f, hf, minimum⟩ := boundedSpeedCurves_minimum a b K ⟨first, first_in⟩
  let q : Path a b := ⟨f.toContinuousMap, hf.1, hf.2.1⟩
  have bounded : q.eLength ≤ p.eLength :=
    (q.eLength_le_of_lipschitz hf.2.2).trans_eq (ENNReal.coe_toNNReal finite)
  refine ⟨q, ?_, ne_top_of_le_ne_top finite bounded⟩
  intro other
  by_cases longer : p.eLength ≤ other.eLength
  · exact bounded.trans longer
  · have shorter := lt_of_not_ge longer
    have finite_other : other.eLength ≠ ⊤ := ne_top_of_lt shorter
    obtain ⟨replacement, replacement_speed, _, length_bound⟩ :=
      other.exists_lipschitz_reparameterization finite_other
    let g : unitInterval →ᵇ X := mkOfCompact replacement.toContinuousMap
    have g_in : g ∈ boundedSpeedCurves a b K :=
      ⟨replacement.source, replacement.target,
        replacement_speed.weaken
          ((ENNReal.toNNReal_le_toNNReal finite_other finite).mpr shorter.le)⟩
    have comparison : q.eLength ≤ replacement.eLength := minimum g g_in
    exact comparison.trans length_bound

/-- A shortest path can be chosen with the speed bound used in geodesic arguments. -/
theorem exists_lengthMinimizing_lipschitz {a b : X} (p : Path a b) (finite : p.eLength ≠ ⊤) :
    ∃ q : Path a b, q.IsLengthMinimizing ∧ q.eLength ≠ ⊤ ∧ LipschitzWith q.eLength.toNNReal q := by
  obtain ⟨q, minimal, qfinite⟩ := p.exists_lengthMinimizing finite
  obtain ⟨replacement, speed, _, bound⟩ := q.exists_lipschitz_reparameterization qfinite
  have equal : replacement.eLength = q.eLength := le_antisymm bound (minimal replacement)
  exact ⟨replacement, fun other => bound.trans (minimal other), equal ▸ qfinite, equal ▸ speed⟩

end Path
