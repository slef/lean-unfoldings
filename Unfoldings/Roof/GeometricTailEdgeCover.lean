module

public import Unfoldings.Roof.GeometricTailCoalescence
public import Unfoldings.Topology.ParentOrbitEnumeration

/-! Every point on an actual ancestor edge is on the exact represented tail graph. -/

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
  {leaf w : F.GeometricVertex}

theorem point_eq_of_mem_ancestor_edge
    (G : M.SectorTailGraph F covered positive small i leaf)
    (nonroot : w ∉ (M.geometricParents F covered positive small).roots)
    (ancestor : (M.geometricParents F covered positive small).Ancestor leaf w)
    {x : Plane} (member : x ∈ segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w))) :
    let z := (fiveSectorFrame t positive small i).place (x - origin)
    G.graph.point (z.re + z.im) = z := by
  let Q := M.geometricParents F covered positive small
  let B := fiveSectorFrame t positive small i
  let A := centeredPlaneFrame (origin) B.place
  let P := M.geometricRootPath F covered positive small B.place leaf
  let j := (Q.nonrootAncestorEquiv leaf).symm ⟨w, nonroot, ancestor⟩
  have at_w : (M.geometricParent F covered)^[j.val] leaf = w :=
    congrArg Subtype.val ((Q.nonrootAncestorEquiv leaf).apply_symm_apply ⟨w, nonroot, ancestor⟩)
  have first : A (F.geometricPosition w) = P.vertex j.castSucc := by
    change A (F.geometricPosition w) = B.place
      (F.geometricPosition ((M.geometricParent F covered)^[j.val] leaf) - origin)
    rw [at_w]
    exact centeredPlaneFrame_apply _ _ _
  have last : A (F.geometricPosition (M.geometricParent F covered w)) = P.vertex j.succ := by
    change A (F.geometricPosition (M.geometricParent F covered w)) = B.place
      (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] leaf) -
        origin)
    rw [Function.iterate_succ_apply', at_w]
    exact centeredPlaneFrame_apply _ _ _
  have image : A '' segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w)) =
        segment ℝ (A (F.geometricPosition w))
          (A (F.geometricPosition (M.geometricParent F covered w))) :=
    image_segment ℝ A.toAffineMap _ _
  have on_segment := image.subset ⟨x, member, rfl⟩
  rw [first, last, segment_eq_image_lineMap] at on_segment
  obtain ⟨s, inside, equal⟩ := on_segment
  let parameter : unitInterval := ⟨s, inside⟩
  have on_path : P.point j parameter = A x := equal
  have point := G.graph.point_eq_of_coordinate (P.point j parameter) (G.pieces j parameter)
  rw [on_path, centeredPlaneFrame_apply] at point
  exact point

end Unfoldings.ConvexRoof.SectorForest.SectorTailGraph
