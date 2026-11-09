module

public import Unfoldings.Source.OffCutCoordinates
public import Unfoldings.Source.ConvexCoordinates

/-!
# Actual continuous injective source coordinates off the convex-surface cut locus

The source frame, shortest-path existence, uniqueness and coordinate
injectivity have all been constructed. This theorem has only the original
convex-boundary input and regularity of the chosen source as hypotheses.
It does not yet claim local metric compatibility or the completed net.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_continuous_injective_source_coordinates (source : C.Realization Set.univ)
    (regular : C.IsRegularPoint Set.univ source) :
    letI := P.metricSpace
    ∃ coordinates : ↥((sourceCutLocus source)ᶜ) → Plane,
      Continuous coordinates ∧ Function.Injective coordinates ∧
        ∀ x, ‖coordinates x‖ = dist source x.val := by
  let := P.metricSpace
  let R : SourceFrame source := sourceFrame regular
  let coordinates := R.coordinatesOffCutLocus (P.sourcePath_target_surjective source)
  exact ⟨coordinates, R.continuous_coordinatesOffCutLocus _,
    R.coordinatesOffCutLocus_injective _ (P.sourcePathCoordinate_injective R),
    R.norm_coordinatesOffCutLocus _⟩

end Unfoldings.SpatialFolding.ConvexBoundary
