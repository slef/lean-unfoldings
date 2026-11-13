module

public import Unfoldings.Roof.CompletionRadialMesh
public import Unfoldings.Roof.CompletionOriginalEdgeCover
public import Unfoldings.Roof.ExtendedGeometricCuts
public import Unfoldings.Roof.SpatialEnvelopeInteriorSeams

/-! The constructed original and skirt cut set is an actual union of removed physical seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

theorem extended_cut_fine_edge {p : Plane}
    (member : p ∈ M.extendedGeometricCuts (E.cornerTails M.inside))
    (inside : p ∈ interior
      (SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level)) :
    let L := E.radialMesh M.inside
    ∃ a : EdgeRef L.mesh.Index,
      p ∈ (L.mesh.projectedTriangle a.face).edge a.edge ∧
        (L.mesh.projectedTriangle a.face).edge a.edge ⊆
          M.extendedGeometricCuts (E.cornerTails M.inside) := by
  let F := E.cornerTails M.inside
  let L := E.radialMesh M.inside
  rcases member with original | skirt
  · obtain ⟨e, on_parent⟩ := Set.mem_iUnion.mp original
    let s := M.selection.edge e
    have on_old_edge := (M.parent_segment_eq_original_seam e).subset on_parent
    have cover := L.originalPart.original_edge_eq_union_subedges (C.left s).face (C.left s).edge
    obtain ⟨a, on_fine⟩ := Set.mem_iUnion.mp (cover.subset on_old_edge)
    refine ⟨⟨a.val.1, a.val.2⟩, on_fine, fun x hx => Or.inl ?_⟩
    exact Set.mem_iUnion.mpr ⟨e,
      (M.parent_segment_eq_original_seam e).symm.subset (a.property hx)⟩
  · obtain ⟨c, on_component⟩ := Set.mem_iUnion.mp skirt
    by_cases different : F.componentSeed c ≠ (F.componentTail c).tip
    · let a : F.Active := ⟨c, different⟩
      have cover := E.radialMesh_component_cover M.inside a
      obtain ⟨e, on_fine⟩ := Set.mem_iUnion.mp (cover.subset on_component)
      exact ⟨⟨e.val.1, e.val.2⟩, on_fine,
        fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨c, e.property hx⟩)⟩
    · have singleton : (F.componentTail c).carrier = {(F.componentTail c).tip} := by
        change segment ℝ (F.componentSeed c) (F.componentTail c).tip = _
        exact (congrArg (fun x : Plane => segment ℝ x (F.componentTail c).tip)
          (not_ne_iff.mp different)).trans (segment_same ℝ _)
      have at_tip := singleton.subset on_component
      exact ((F.componentTail c).boundary.2 ((Set.mem_singleton_iff.mp at_tip) ▸ inside)).elim

def extendedRetain :
    letI := @Fintype.ofFinite _ (E.radialMesh M.inside).mesh.finite
    Set (E.radialMesh M.inside).mesh.toTriangulation.pairedComplex.Seam :=
  letI := @Fintype.ofFinite _ (E.radialMesh M.inside).mesh.finite
  (E.radialMesh M.inside).mesh.toTriangulation.retainOutside
    (M.extendedGeometricCuts (E.cornerTails M.inside))

theorem extended_cut_seam {p : Plane}
    (member : p ∈ M.extendedGeometricCuts (E.cornerTails M.inside))
    (inside : p ∈ interior
      (SpatialEnvelope.clip (K.completionPlanes E.tentHeight (Real.sin φ / 2)) E.level)) :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    ∃ s : L.mesh.toTriangulation.pairedComplex.Seam, s ∉ M.extendedRetain E ∧
      p ∈ (L.mesh.projectedTriangle (L.mesh.toTriangulation.pairedComplex.left s).face).edge
        (L.mesh.toTriangulation.pairedComplex.left s).edge := by
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  obtain ⟨a, on_edge, selected⟩ := M.extended_cut_fine_edge E member inside
  obtain ⟨s, cut, incident⟩ := L.mesh.toTriangulation.exists_cut_seam_of_projected_edge
    L.conforming L.interior_nonempty (M.extendedGeometricCuts (E.cornerTails M.inside))
    a selected on_edge inside
  refine ⟨s, cut, ?_⟩
  rcases incident with first | last
  · simpa only [first] using on_edge
  · rw [L.mesh.toTriangulation.paired_seam_projected_edge]
    simpa only [last] using on_edge

end Unfoldings.ConvexRoof.SectorForest
