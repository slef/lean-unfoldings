module

public import Unfoldings.Roof.GeometricComponentPieces
public import Unfoldings.Roof.GeometricRadialEdges
public import Unfoldings.Roof.GeometricSectorNetwork

/-! Physical component cut pieces belong to the actual deterministic sector network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricComponentSector

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {c : F.Component}
  (data : M.GeometricComponentSector F covered positive small c)

/-- This covers whole original edges and whole radial continuations, independently
of the later roof triangulation and its selected fine parent edges. -/
theorem cut_piece_mem_heightNetwork
    (genuine : F.componentSeed c ≠ (F.componentTail c).tip)
    (j : M.ExtendedCutPiece F) (same : M.cutPieceLabel F covered j = c)
    {p : Plane} (member : p ∈ segment ℝ (M.cutPieceFirst F j) (M.cutPieceLast F j)) :
    (fiveSectorFrame t positive small data.sector).place (p - origin) ∈
      (M.sectorHeightNetwork F covered positive small data.sector).carrier := by
  let A := centeredPlaneFrame (origin)
    (fiveSectorFrame t positive small data.sector).place
  have represented (w : F.GeometricVertex)
      (nonroot : w ∉ (M.geometricParents F covered positive small).roots)
      (component : M.geometricComponent F covered w = c)
      (inside : p ∈ segment ℝ (F.geometricPosition w)
        (F.geometricPosition (M.geometricParent F covered w))) :
      A p ∈ (M.sectorHeightNetwork F covered positive small data.sector).carrier := by
    let e : M.GeometricSectorEdge F covered positive small data.sector :=
      ⟨w, nonroot, data.directions w nonroot component⟩
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    have image := image_segment ℝ A.toAffineMap (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))
    exact image.subset ⟨p, inside, rfl⟩
  rw [← centeredPlaneFrame_apply]
  change A p ∈ (M.sectorHeightNetwork F covered positive small data.sector).carrier
  cases j with
  | inl e =>
    have internal : ¬ C.IsBoundaryVertex Set.univ e.val := by
      simpa only [M.roots_eq, Set.mem_ofPred_eq] using e.property
    apply represented (Sum.inl e.val)
      (M.geometric_original_nonroot F covered positive small e.val) same
    have parent : M.geometricParent F covered (Sum.inl e.val) =
        Sum.inl (M.parents.parent e.val) :=
      M.geometricParents_original_parent F covered positive small e.val internal
    rw [parent]
    exact member
  | inr d =>
    change d = c at same
    subst d
    obtain ⟨w, nonroot, component, seed, parent⟩ :=
      M.exists_geometric_component_radial_edge F covered positive small c genuine
    apply represented w nonroot component
    rw [seed, parent]
    exact member

end Unfoldings.ConvexRoof.SectorForest.GeometricComponentSector
