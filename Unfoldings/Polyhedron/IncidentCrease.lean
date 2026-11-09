module

public import Unfoldings.Polyhedron.NonextremePlanes
public import Unfoldings.Cone.LinkSeams

/-! Distinct incident planes force an actual crease in the cyclic vertex link. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_incident_crease {v : C.Vertex Set.univ}
    (a b : C.CornerAt Set.univ v)
    (different : LinearMap.range (F.place a.val.1).linear ≠
      LinearMap.range (F.place b.val.1).linear) :
    ∃ s : C.TangentSeam Set.univ v,
      LinearMap.range (F.place (C.tangentLeft Set.univ v s).val.1).linear ≠
        LinearMap.range (F.place (C.tangentRight Set.univ v s).val.1).linear := by
  classical
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link v
  obtain ⟨i, at_i⟩ := (C.linkCornerEquiv Set.univ v c covers).surjective a
  obtain ⟨j, at_j⟩ := (C.linkCornerEquiv Set.univ v c covers).surjective b
  let label (k : Fin (n + 1)) := LinearMap.range (F.place (c.point k).val.1.1).linear
  have distinct : label i ≠ label j := by
    change LinearMap.range (F.place ((C.linkCornerEquiv Set.univ v c covers) i).val.1).linear ≠
      LinearMap.range (F.place ((C.linkCornerEquiv Set.univ v c covers) j).val.1).linear
    rwa [at_i, at_j]
  obtain ⟨k, value, entry⟩ := exists_cyclic_label_entry label (label i)
    ⟨i, rfl⟩ ⟨j, distinct.symm⟩
  have changes : LinearMap.range (F.place (c.point k).val.1.1).linear ≠
      LinearMap.range (F.place (C.linkMate Set.univ v (c.point k)).val.1.1).linear := by
    rw [F.linkPlane_mate_eq_prev c closes k]
    change label k ≠ label ((finRotate (n + 1)).symm k)
    rw [value]
    exact entry.symm
  have moved : C.mateGerm Set.univ (c.point k).val ≠ (c.point k).val := by
    intro fixed
    have equal : C.linkMate Set.univ v (c.point k) = c.point k := Subtype.ext fixed
    exact changes (congrArg (fun p : C.LinkGerm Set.univ v =>
      LinearMap.range (F.place p.val.1.1).linear) equal.symm)
  obtain ⟨s, kept, side, endpoint, source, target⟩ :=
    C.germCrosses_mate_of_ne Set.univ (c.point k).val moved
  have vertex : C.vertexOfCorner Set.univ
      (C.germOfEndpoint (C.seamSide s side) endpoint).1 = v := by
    rw [← source]
    exact (c.point k).property
  let seam : C.TangentSeam Set.univ v := ⟨(s, side, endpoint), kept, vertex⟩
  refine ⟨seam, ?_⟩
  change LinearMap.range
    (F.place (C.germOfEndpoint (C.seamSide s side) endpoint).1.1).linear ≠
      LinearMap.range (F.place (C.germOfEndpoint (C.seamSide s (!side))
        (C.acrossEndpoint s side endpoint)).1.1).linear
  rw [← source, ← target]
  exact changes

end Unfoldings.SpatialFolding.ConvexBoundary
