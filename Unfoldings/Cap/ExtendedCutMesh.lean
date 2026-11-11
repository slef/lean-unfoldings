module

public import Unfoldings.Cap.ExtendedCutCurvature
public import Unfoldings.Cap.ClipInteriorSeams

/-! The extended geometric cut set selects actual whole fine edges and actual removed seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} {q : Plane}

def extendedGeometricCuts (F : K.SkirtTailFamily Z q) : Set Plane :=
  M.projectedCutCarrier ∪ ⋃ c : F.Component, (F.componentTail c).carrier

/-- Every interior point of the constructed geometric cuts lies on a whole selected fine edge. -/
theorem extended_cut_fine_edge (T : K.ClipSpatialTriangles Z) (F : K.SkirtTailFamily Z q)
    (lower : Z < 0) {p : Plane} (member : p ∈ M.extendedGeometricCuts F)
    (inside : p ∈ interior (K.clipFootprint Z)) :
    let L := F.mesh T lower
    ∃ a : EdgeRef L.partition.Index,
      p ∈ (L.partition.projectedTriangle a.face).edge a.edge ∧
        (L.partition.projectedTriangle a.face).edge a.edge ⊆ M.extendedGeometricCuts F := by
  let L := F.mesh T lower
  rcases member with original | skirt
  · obtain ⟨e, on_parent⟩ := Set.mem_iUnion.mp original
    let s := M.selection.edge e
    have on_old_edge := (M.parent_segment_eq_original_seam e).subset on_parent
    have cover := L.originalPart.original_edge_eq_union_subedges lower
      (C.left s).face (C.left s).edge
    obtain ⟨a, on_fine⟩ := Set.mem_iUnion.mp (cover.subset on_old_edge)
    refine ⟨⟨a.val.1, a.val.2⟩, on_fine, fun x hx => Or.inl ?_⟩
    exact Set.mem_iUnion.mpr ⟨e,
      (M.parent_segment_eq_original_seam e).symm.subset (a.property hx)⟩
  · obtain ⟨c, on_component⟩ := Set.mem_iUnion.mp skirt
    by_cases different : F.componentSeed c ≠ (F.componentTail c).tip
    · let a : F.Active := ⟨c, different⟩
      have cover := L.segment_eq_union_subedges a (F.component_member c) (F.component_tip_member c)
      obtain ⟨e, on_fine⟩ := Set.mem_iUnion.mp (cover.subset on_component)
      exact ⟨⟨e.val.1, e.val.2⟩, on_fine,
        fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨c, e.property hx⟩)⟩
    · have singleton : (F.componentTail c).carrier = {(F.componentTail c).tip} := by
        change segment ℝ (F.componentSeed c) (F.componentTail c).tip = _
        exact (congrArg (fun x : Plane => segment ℝ x (F.componentTail c).tip)
          (not_ne_iff.mp different)).trans (segment_same ℝ _)
      have at_tip := singleton.subset on_component
      exact ((F.componentTail c).boundary.2 ((Set.mem_singleton_iff.mp at_tip) ▸ inside)).elim

local instance extendedMeshIndexFintype (T : K.ClipSpatialTriangles Z)
    (F : K.SkirtTailFamily Z q) (lower : Z < 0) :
    Fintype (F.mesh T lower).partition.Index :=
  @Fintype.ofFinite _ (F.mesh T lower).partition.finite

/-- The actual retained-seam set obtained by cutting every selected whole fine edge. -/
def extendedRetain (T : K.ClipSpatialTriangles Z) (F : K.SkirtTailFamily Z q) (lower : Z < 0) :
    Set (F.mesh T lower).partition.pairedComplex.Seam :=
  (F.mesh T lower).partition.retainOutside (M.extendedGeometricCuts F)

/-- Every interior geometric cut point belongs to an actual removed whole seam. -/
theorem extended_cut_seam (T : K.ClipSpatialTriangles Z) (F : K.SkirtTailFamily Z q)
    (lower : Z < 0) {p : Plane} (member : p ∈ M.extendedGeometricCuts F)
    (inside : p ∈ interior (K.clipFootprint Z)) :
    let L := F.mesh T lower
    ∃ s : L.partition.pairedComplex.Seam, s ∉ M.extendedRetain T F lower ∧
      p ∈ (L.partition.projectedTriangle (L.partition.pairedComplex.left s).face).edge
        (L.partition.pairedComplex.left s).edge := by
  let L := F.mesh T lower
  obtain ⟨a, on_edge, selected⟩ := M.extended_cut_fine_edge T F lower member inside
  obtain ⟨s, cut, incident⟩ := L.partition.exists_cut_seam_of_projected_edge L.conforming lower
    (M.extendedGeometricCuts F) a selected on_edge inside
  refine ⟨s, cut, ?_⟩
  rcases incident with first | last
  · simpa only [first] using on_edge
  · rw [L.partition.paired_seam_projected_edge]
    simpa only [last] using on_edge

end Unfoldings.ConvexCap.SectorForest
