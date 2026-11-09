module

public import Unfoldings.Source.ConvexCoordinates
public import Unfoldings.Source.Domain

/-! Every regular convex-boundary source has a constructed compact planar ray domain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def sourceDomainHomeomorph :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → (R : SourceFrame source) →
      SourcePath source ≃ₜ R.domain := by
  let := P.metricSpace
  intro source R
  exact R.coordinateHomeomorph (P.sourcePathCoordinate_injective R)

theorem sourceProjection_surjective :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      Function.Surjective (R.projection (P.sourcePathCoordinate_injective R)) := by
  let := P.metricSpace
  intro source R
  exact R.projection_surjective (P.sourcePathCoordinate_injective R)
    (P.sourcePath_target_surjective source)

end Unfoldings.SpatialFolding.ConvexBoundary
