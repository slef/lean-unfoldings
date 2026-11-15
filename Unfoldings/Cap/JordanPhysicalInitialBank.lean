module

public import Unfoldings.Cap.JordanInitialSeamBank
public import Unfoldings.Cap.ProjectedUnsignedBankRays

/-! The unique selected initial Jordan side keeps the original full physical bank geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- Curve geometry chooses an actual bank in one of the two original incident face sides.
No initial selected-side or orientation assumption is supplied. -/
theorem exists_jordan_bank_on_either_original_side (p : C.Germ)
    (paired : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p))
    (on_curve : (K.projectedTriangle p.1.1).edge (C.germEdge p).edge ⊆ J) :
    ∃ q : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ,
      C.includeRestrictedGerm (K.jordanFaces J) q.val = p ∨
        C.includeRestrictedGerm (K.jordanFaces J) q.val = C.mateGerm Set.univ p := by
  obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff Set.univ p).mpr paired
  obtain ⟨s, _kept, side, flag, rfl, rfl⟩ := crossing
  have crossing : C.GermCrosses Set.univ
      (C.germOfEndpoint (C.seamSide s side) flag)
      (C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side flag)) :=
    ⟨s, Set.mem_univ _, side, flag, rfl, rfl⟩
  have first_curve : (K.projectedTriangle (C.seamSide s side).face).edge
      (C.seamSide s side).edge ⊆ J := by
    simpa only [C.germEdge_germOfEndpoint] using! on_curve
  have same_edges : (K.projectedTriangle (C.seamSide s side).face).edge (C.seamSide s side).edge =
      (K.projectedTriangle (C.seamSide s (!side)).face).edge (C.seamSide s (!side)).edge := by
    cases side
    · exact K.projected_seam_edges_eq s
    · exact (K.projected_seam_edges_eq s).symm
  have last_curve := same_edges.symm.subset.trans first_curve
  have selected : (C.seamSide s side).face ∈ K.jordanFaces J ∨
      (C.seamSide s (!side)).face ∈ K.jordanFaces J := by
    cases side
    · exact K.jordan_seam_incident_selected jordan contains avoids s first_curve
    · exact (K.jordan_seam_incident_selected jordan contains avoids s last_curve).symm
  rcases selected with first | last
  · obtain ⟨q, named⟩ := K.exists_jordan_bank_of_original_germ jordan contains avoids
      (C.germOfEndpoint (C.seamSide s side) flag) first on_curve
    exact ⟨q, Or.inl named⟩
  · have last_raw_curve : (K.projectedTriangle
        (C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side flag)).1.1).edge
        (C.germEdge (C.germOfEndpoint (C.seamSide s (!side))
          (C.acrossEndpoint s side flag))).edge ⊆ J := by
      simpa only [C.germEdge_germOfEndpoint] using! last_curve
    obtain ⟨q, named⟩ := K.exists_jordan_bank_of_original_germ jordan contains avoids
      (C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side flag)) last last_raw_curve
    exact ⟨q, Or.inr (named.trans (C.mateGerm_of_crossing crossing).symm)⟩

include jordan contains avoids in
open Classical in
/-- The selected initial bank has exactly the prescribed original spatial position and
full edge vector, even when its incident face is the opposite original seam side. -/
theorem exists_jordan_initial_physical_bank (p : C.Germ)
    (paired : ¬ C.IsBoundaryEdge Set.univ (C.germEdge p))
    (on_curve : (K.projectedTriangle p.1.1).edge (C.germEdge p).edge ⊆ J) :
    ∃ q : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ,
      (K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition q =
        K.folding.toSpace Set.univ (C.vertexPoint Set.univ (C.vertexOfCorner Set.univ p.1)) ∧
      (K.folding.restrictFaces (K.jordanFaces J)).germDirection q.val =
        K.folding.germDirection p := by
  obtain ⟨q, named⟩ := K.exists_jordan_bank_on_either_original_side jordan contains avoids
    p paired on_curve
  have position : (K.folding.restrictFaces (K.jordanFaces J)).boundaryPosition q =
      K.folding.toSpace Set.univ (C.vertexPoint Set.univ
        (C.vertexOfCorner Set.univ (C.includeRestrictedGerm (K.jordanFaces J) q.val).1)) := by
    rw [SpatialFolding.boundaryPosition_raw]
    rfl
  refine ⟨q, ?_, ?_⟩
  · rw [position]
    rcases named with same | same
    · rw [same]
    · rw [same, C.mateGerm_vertex_eq]
  · change K.folding.germDirection (C.includeRestrictedGerm (K.jordanFaces J) q.val) = _
    rcases named with same | same
    · rw [same]
    · rw [same, K.folding.germDirection_mate]

end Unfoldings.ConvexCap
