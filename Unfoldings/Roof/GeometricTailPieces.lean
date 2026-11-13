module

public import Unfoldings.Roof.GeometricTailCoalescence
public import Unfoldings.Roof.GeometricCutIncidence

/-! Every covered actual tail point lies on a labeled geometric parent edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outer : Set Plane} {F : K.SkirtTailFamily outer (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  {w : F.GeometricVertex}

theorem exists_parent_edge_at_point (G : M.SectorTailGraph F covered positive small i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small i w ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small i w)
    {p : Plane} (at_point : G.graph.point h = (fiveSectorFrame t positive small i).place
      (p - origin)) :
    ∃ v : F.GeometricVertex,
      v ∉ (M.geometricParents F covered positive small).roots ∧
      (M.geometricParents F covered positive small).Ancestor w v ∧
      p ∈ segment ℝ (F.geometricPosition v)
        (F.geometricPosition (M.geometricParent F covered v)) := by
  let B := fiveSectorFrame t positive small i
  let P := M.geometricRootPath F covered positive small B.place w
  let Q := M.geometricParents F covered positive small
  obtain ⟨j, s, on_path⟩ := P.heightGraph_point_on_chain G.graph G.pieces
    (fun j => add_pos (G.positive_steps j).1 (G.positive_steps j).2) h start finish
  let v := (M.geometricParent F covered)^[j.val] w
  let A := centeredPlaneFrame (origin) B.place
  have first : A (F.geometricPosition v) = P.vertex j.castSucc := centeredPlaneFrame_apply _ _ _
  have last : A (F.geometricPosition (M.geometricParent F covered v)) = P.vertex j.succ := by
    calc
      _ = B.place (F.geometricPosition (M.geometricParent F covered v) -
          origin) := centeredPlaneFrame_apply _ _ _
      _ = P.vertex j.succ := by
        change B.place (F.geometricPosition (M.geometricParent F covered v) -
          origin) = B.place
            (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] w) -
              origin)
        rw [Function.iterate_succ_apply']
  have position : A (p) = P.point j s :=
    (centeredPlaneFrame_apply _ _ _).trans (at_point.symm.trans on_path)
  have coordinate_member : A (p) ∈
      segment ℝ (A (F.geometricPosition v))
        (A (F.geometricPosition (M.geometricParent F covered v))) := by
    rw [position, first, last]
    exact lineMap_mem_segment ℝ _ _ s.property
  have image : A '' segment ℝ (F.geometricPosition v)
      (F.geometricPosition (M.geometricParent F covered v)) =
      segment ℝ (A (F.geometricPosition v))
        (A (F.geometricPosition (M.geometricParent F covered v))) :=
    image_segment ℝ A.toAffineMap _ _
  obtain ⟨y, inside, equal⟩ := image.symm.subset coordinate_member
  have physical : p ∈ segment ℝ (F.geometricPosition v)
      (F.geometricPosition (M.geometricParent F covered v)) := A.injective equal ▸ inside
  have nonroot : v ∉ Q.roots := Q.iterate_lt_distanceToRoot_not_mem w j.isLt
  exact ⟨v, nonroot, ⟨j.val, rfl⟩, physical⟩

/-- The tail's original component label is retained at every intermediate point. -/
theorem labeled_piece_of_point (G : M.SectorTailGraph F covered positive small i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small i w ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small i w)
    {p : Plane} (at_point : G.graph.point h = (fiveSectorFrame t positive small i).place
      (p - origin)) :
    ∃ piece : M.ExtendedCutPiece F,
      M.cutPieceLabel F covered piece = M.geometricComponent F covered w ∧
      p ∈ segment ℝ (M.cutPieceFirst F piece) (M.cutPieceLast F piece) := by
  obtain ⟨v, nonroot, ⟨n, equal⟩, member⟩ := G.exists_parent_edge_at_point start finish at_point
  obtain ⟨piece, first, last, label⟩ := M.geometric_parent_piece F covered positive small
    v nonroot
  have component : M.geometricComponent F covered v = M.geometricComponent F covered w := by
    rw [← equal]
    exact M.geometricComponent_iterate F covered w n
  refine ⟨piece, label.trans component, ?_⟩
  rwa [first, last]

end Unfoldings.ConvexRoof.SectorForest.SectorTailGraph
