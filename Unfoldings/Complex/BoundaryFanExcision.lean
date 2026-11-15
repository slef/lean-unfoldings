module

public import Unfoldings.Complex.RestoredLinkChain
public import Unfoldings.Complex.Star

/-! Surviving terminal banks preserve whole intrinsic balls under actual cut restoration. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  (p : C.BoundaryEnd small)
  (first : C.IsBoundaryEdge large (C.germEdge p.val))
  (last : C.IsBoundaryEdge large (C.germEdge (C.boundaryMate small p).val))

include inclusion first last in
/-- Every actual retained seam incident to this restored fan was already retained before.
The two original outer bank germs prevent a hidden seam from closing or enlarging the fan. -/
theorem boundary_fan_keeps_incident :
    ∀ s ∈ large, C.SeamIncident large (C.cornerPoint p.val.1) s → s ∈ small := by
  intro s kept incident
  have in_star := C.vertexStar_keeps_incident large p.val.1 s kept incident
  obtain ⟨_, b, endpoint⟩ := (C.mem_vertexStarSeams_iff large _ s).mp in_star
  have actual : C.vertexOfCorner small (C.germOfEndpoint (C.left s) b).1 =
      C.boundaryEndVertex small p :=
    (C.boundary_fan_corners_iff inclusion p first last _).mp endpoint
  by_contra cut
  have boundary : C.IsBoundaryEdge small (C.left s) :=
    (C.isBoundaryEdge_left_iff small s).mpr cut
  let q : C.BoundaryEnd small := ⟨C.germOfEndpoint (C.left s) b, by
    rw [C.germEdge_germOfEndpoint]
    exact boundary⟩
  have same : C.boundaryEndVertex small q = C.boundaryEndVertex small p := actual
  have outer : C.IsBoundaryEdge large (C.germEdge q.val) := by
    rcases (C.boundaryEnd_vertex_eq_iff small q p).mp same with equal | equal
    · exact equal.symm ▸ first
    · exact equal.symm ▸ last
  have old_boundary : C.IsBoundaryEdge large (C.left s) := by
    simpa only [q, C.germEdge_germOfEndpoint] using outer
  exact (C.isBoundaryEdge_left_iff large s).mp old_boundary kept

include first last in
/-- The isometry is the canonical restoration of the original faces and seams on a whole ball,
including its boundary banks. No tangent model or prescribed radius is assumed. -/
theorem exists_boundary_fan_forgetChart :
    Nonempty (MetricGluing.ForgetChart C.Cell (C.glue_mono inclusion) (C.cornerPoint p.val.1)) :=
  C.exists_localForgetChart inclusion (C.cornerPoint p.val.1)
    (C.boundary_fan_keeps_incident inclusion p first last)

end Unfoldings.TriangleComplex
