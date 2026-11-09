module

public import Unfoldings.Source.FaceAtlas
public import Unfoldings.Path.Restriction

/-! Actual face motions agree at the endpoints of any retained face path. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem sourceFaceMotion_eq_along_path :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source) (f : Face)
      {a b : C.Cell f} (q : Path a b),
      (∀ t, C.faceMap Set.univ f (q t) ∉ sourceCutLocus source) →
      ∀ off_a : C.faceMap Set.univ f a ∉ sourceCutLocus source,
        ∀ off_b : C.faceMap Set.univ f b ∉ sourceCutLocus source,
          P.sourceFaceMotion R f ⟨a, off_a⟩ = P.sourceFaceMotion R f ⟨b, off_b⟩ := by
  let := P.metricSpace
  intro source R f a b q outside off_a off_b
  let path := q.codRestrict (P.sourceFaceRegion source f) off_a off_b outside
  have locally_constant := (P.sourceFaceMotion_locallyConstant R f).comp_continuous path.continuous
  have equal := locally_constant.apply_eq_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (0 : unitInterval)) (Set.mem_univ (1 : unitInterval))
  simpa only [Function.comp_apply, Path.source, Path.target] using equal

end Unfoldings.SpatialFolding.ConvexBoundary
