module

public import Unfoldings.Source.BoundaryImages

/-! Every actual source endpoint has finitely many normalized shortest paths and boundary copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

theorem finite_sourcePath_fiber :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (_R : SourceFrame source)
      (target : C.Realization Set.univ), Finite {p : SourcePath source // p.target = target} := by
  let := P.metricSpace
  intro source R target
  obtain ⟨M, finite, images⟩ := P.exists_finite_all_source_vectors R
  obtain ⟨⟨f, y⟩, target_image⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) target
  let V := (fun A : Plane ≃ᵃⁱ[ℝ] Plane => A y.val) '' M
  let : Finite V := (finite.image (fun A : Plane ≃ᵃⁱ[ℝ] Plane => A y.val)).to_subtype
  let map (p : {p : SourcePath source // p.target = target}) : V :=
    ⟨R.coordinate p.val.path p.val.geodesic, by
      obtain ⟨A, member, coordinate⟩ := images p.val f y (p.property.trans target_image.symm)
      exact ⟨A, member, coordinate.symm⟩⟩
  apply Finite.of_injective map
  intro p q equal
  apply Subtype.ext
  exact P.sourcePathCoordinate_injective R (congrArg Subtype.val equal)

end Unfoldings.SpatialFolding.ConvexBoundary
