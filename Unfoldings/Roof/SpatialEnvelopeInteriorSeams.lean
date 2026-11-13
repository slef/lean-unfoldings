module

public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Geometry.SpatialEnvelopeCuts

/-! Whole physical edges meeting the completion interior have actual seam partners. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance spatialInteriorSeamIndexFintype : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

theorem exists_seam_of_projected_edge_interior
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (nonempty : (interior (clip family Z)).Nonempty)
    (a : EdgeRef T.Index) {p : Plane} (on_edge : p ∈ (T.projectedTriangle a.face).edge a.edge)
    (inside : p ∈ interior (clip family Z)) :
    ∃ s : T.pairedComplex.Seam, T.pairedComplex.Incident s a := by
  classical
  by_contra absent
  have boundary : T.pairedComplex.IsBoundaryEdge Set.univ a := by
    rintro ⟨s, _kept, incident⟩
    exact absent ⟨s, incident⟩
  let bank : T.pairedComplex.BoundaryBank Set.univ := ⟨a, boundary⟩
  let x := (T.edgeProjection a.face a.edge).symm ⟨p, on_edge⟩
  have present : T.pairedComplex.bankMap Set.univ bank x ∈
      T.pairedComplex.bankBoundary Set.univ := Set.mem_iUnion.mpr ⟨bank, x, rfl⟩
  let Q := T.roof conforming nonempty
  have on_frontier := (Q.projected_mem_frontier_iff_bankBoundary _).mpr present
  change Cap.horizontal (T.pairedFolding.toSpace Set.univ
    (T.pairedComplex.bankMap Set.univ bank x)) ∈ frontier Q.footprint at on_frontier
  have projected : Cap.horizontal (T.pairedFolding.toSpace Set.univ
      (T.pairedComplex.bankMap Set.univ bank x)) = p := by
    change Cap.horizontal ((family (T.support a.face)).place x.val) = p
    rw [(family (T.support a.face)).horizontal_place]
    exact (family (T.support a.face)).project.apply_symm_apply p
  have footprint : Q.footprint = clip family Z := T.pairedFolding_footprint
  rw [projected, footprint] at on_frontier
  exact on_frontier.2 inside

theorem exists_cut_seam_of_projected_edge
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (nonempty : (interior (clip family Z)).Nonempty)
    (cuts : Set Plane) (a : EdgeRef T.Index)
    (selected : (T.projectedTriangle a.face).edge a.edge ⊆ cuts)
    {p : Plane} (on_edge : p ∈ (T.projectedTriangle a.face).edge a.edge)
    (inside : p ∈ interior (clip family Z)) :
    ∃ s : T.pairedComplex.Seam, s ∉ T.retainOutside cuts ∧ T.pairedComplex.Incident s a := by
  obtain ⟨s, incident⟩ := T.exists_seam_of_projected_edge_interior conforming nonempty a
    on_edge inside
  refine ⟨s, fun kept => kept ?_, incident⟩
  rcases incident with first | last
  · simpa only [first] using selected
  · rw [T.paired_seam_projected_edge]
    simpa only [last] using selected

end Unfoldings.SpatialEnvelope.Triangulation
