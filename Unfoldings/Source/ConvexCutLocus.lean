module

public import Unfoldings.Source.CutLocus
public import Unfoldings.Polyhedron.Convex

/-! Actual unique shortest paths on the complement of the closed convex-surface source cut locus. -/

@[expose] public section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem exists_unique_geodesic_off_cutLocus :
    letI := P.metricSpace
    ∀ {source target : C.Realization Set.univ}, target ∉ sourceCutLocus source →
      ∃! p : Path source target, p.IsGeodesic := by
  let := P.metricSpace
  intro source target outside
  obtain ⟨p, geodesic⟩ := P.exists_geodesic source target
  exact ⟨p, geodesic, fun q other => geodesic_unique_off_cutLocus outside other geodesic⟩

end Unfoldings.SpatialFolding.ConvexBoundary
