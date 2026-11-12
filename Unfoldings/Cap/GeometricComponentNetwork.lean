module

public import Unfoldings.Cap.GeometricComponentPieces
public import Unfoldings.Cap.GeometricRadialEdges
public import Unfoldings.Cap.GeometricSectorNetwork

/-! Physical component cut pieces belong to the actual deterministic sector network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricComponentSector

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {c : F.Component}
  (data : M.GeometricComponentSector F covered positive small lower c)

/-- This covers whole original edges and whole radial continuations, independently
of the later roof triangulation and its selected fine parent edges. -/
theorem cut_piece_mem_heightNetwork
    (genuine : F.componentSeed c ≠ (F.componentTail c).tip)
    (j : M.ExtendedCutPiece F) (same : M.cutPieceLabel F covered j = c)
    {p : Plane} (member : p ∈ segment ℝ (M.cutPieceFirst F j) (M.cutPieceLast F j)) :
    (fiveSectorFrame t positive small data.sector).place (p - K.projectedVertex origin) ∈
      (M.sectorHeightNetwork F covered positive small lower data.sector).carrier := by
  let A := centeredPlaneFrame (K.projectedVertex origin)
    (fiveSectorFrame t positive small data.sector).place
  have represented (w : F.GeometricVertex)
      (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots)
      (component : M.geometricComponent F covered w = c)
      (inside : p ∈ segment ℝ (F.geometricPosition w)
        (F.geometricPosition (M.geometricParent F covered w))) :
      A p ∈ (M.sectorHeightNetwork F covered positive small lower data.sector).carrier := by
    let e : M.GeometricSectorEdge F covered positive small lower data.sector :=
      ⟨w, nonroot, data.directions w nonroot component⟩
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    have image := image_segment ℝ A.toAffineMap (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))
    exact image.subset ⟨p, inside, rfl⟩
  rw [← centeredPlaneFrame_apply]
  change A p ∈ (M.sectorHeightNetwork F covered positive small lower data.sector).carrier
  cases j with
  | inl e =>
    have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
      simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
    apply represented (Sum.inl e.val)
      (M.geometric_original_nonroot F covered positive small lower e.val) same
    have parent : M.geometricParent F covered (Sum.inl e.val) =
        Sum.inl (M.parents.parent e.val) :=
      M.geometricParents_original_parent F covered positive small lower e.val internal
    rw [parent]
    exact member
  | inr d =>
    change d = c at same
    subst d
    obtain ⟨w, nonroot, component, seed, parent⟩ :=
      M.exists_geometric_component_radial_edge F covered positive small lower c genuine
    apply represented w nonroot component
    rw [seed, parent]
    exact member

end Unfoldings.ConvexCap.SectorForest.GeometricComponentSector
