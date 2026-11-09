module

public import Unfoldings.Source.CutMetric
public import Unfoldings.Source.RegularDevelopment
public import Unfoldings.Metric.PolygonalMap
public import Unfoldings.Metric.LocalInverse

/-!
# The actual surface projection does not increase the source cut metric

The inverse of the constructed interior development is locally isometric in
the original surface metric. These local bounds propagate along allowed
polygonal routes. Density then extends nonexpansion to every boundary copy
of the completed cut surface.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceInterior_inverse_local_isometry :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : interior R.domain),
      ∃ T : Set (interior R.domain), IsOpen T ∧ z ∈ T ∧
        Isometry (fun w : T => (P.sourceInteriorHomeomorph R).symm w.val) := by
  let := P.metricSpace
  intro source R z
  apply inverse_isometric_neighborhood
  obtain ⟨S, open_S, inside, isometry⟩ :=
    P.regular_source_coordinates_local_isometry R ((P.sourceInteriorHomeomorph R).symm z)
  exact ⟨S, open_S, inside, fun a b => isometry a b⟩

theorem sourceInterior_inverse_local_bound :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (z : interior R.domain),
      ∀ᶠ w in 𝓝 z,
        dist ((P.sourceInteriorHomeomorph R).symm w) ((P.sourceInteriorHomeomorph R).symm z) ≤
          dist w z := by
  let := P.metricSpace
  intro source R z
  obtain ⟨T, open_T, inside, isometry⟩ := P.sourceInterior_inverse_local_isometry R z
  filter_upwards [open_T.mem_nhds inside] with w hw
  exact (isometry.dist_eq ⟨w, hw⟩ ⟨z, inside⟩).le

theorem sourceCutInterior_projection_lipschitz :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      LipschitzWith 1
        (R.cutCompletionProjection (P.sourcePathCoordinate_injective R) ∘
          R.cutInteriorInclusion) := by
  let := P.metricSpace
  intro source R
  have bound := PolygonalPoint.lipschitz_of_local_center_bounds
    (P.sourceInteriorHomeomorph R).symm (P.sourceInterior_inverse_local_bound R)
  intro a b
  exact bound a b

theorem sourceCutCompletion_projection_lipschitz :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      LipschitzWith 1 (R.cutCompletionProjection (P.sourcePathCoordinate_injective R)) := by
  let := P.metricSpace
  intro source R
  let projection := R.cutCompletionProjection (P.sourcePathCoordinate_injective R)
  have continuous : Continuous projection := R.continuous_cutCompletionProjection _
  intro a b
  simp only [ENNReal.coe_one, one_mul]
  refine (P.sourceCutInteriorInclusion_dense R).induction_on₂
    (p := fun x y => edist (projection x) (projection y) ≤ edist x y) ?_ ?_ a b
  · exact isClosed_le ((continuous.comp continuous_fst).edist (continuous.comp continuous_snd))
      (continuous_fst.edist continuous_snd)
  · intro x y
    rw [(P.sourceCutInteriorInclusion_isometry R).edist_eq]
    simpa only [ENNReal.coe_one, one_mul, Function.comp_def, projection] using
      P.sourceCutInterior_projection_lipschitz R x y

end Unfoldings.SpatialFolding.ConvexBoundary
