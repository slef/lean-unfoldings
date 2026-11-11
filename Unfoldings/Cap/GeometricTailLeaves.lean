module

public import Unfoldings.Cap.GeometricTailCoalescence
public import Unfoldings.Cap.GeometricLeafAvoidance

/-! A new geometric leaf is strictly separated from every distinct existing tail at its height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  {leaf z : F.GeometricVertex}

/-- At the insertion height a distinct leaf is not on an already active actual tail. -/
theorem leaf_coordinate_ne (G : M.SectorTailGraph F covered positive small lower i z)
    (leaf_nonroot : leaf ∉ (M.geometricParents F covered positive small lower).roots)
    (childless : ∀ child ∉ (M.geometricParents F covered positive small lower).roots,
      M.geometricParent F covered child ≠ leaf) (different : z ≠ leaf)
    (start : M.geometricTailStartHeight F covered positive small lower i z ≤
      M.geometricTailStartHeight F covered positive small lower i leaf)
    (finish : M.geometricTailStartHeight F covered positive small lower i leaf <
      M.geometricTailEndHeight F covered positive small lower i z) :
    G.graph.coordinate (M.geometricTailStartHeight F covered positive small lower i leaf) ≠
      ((fiveSectorFrame t positive small i).place
        (F.geometricPosition leaf - K.projectedVertex origin)).re := by
  intro same
  let B := fiveSectorFrame t positive small i
  let Q := M.geometricParents F covered positive small lower
  let P := M.geometricRootPath F covered positive small lower B.place z
  let x := B.place (F.geometricPosition leaf - K.projectedVertex origin)
  let h := M.geometricTailStartHeight F covered positive small lower i leaf
  have height : x.re + x.im = h := rfl
  have at_leaf : G.graph.point h = x := by
    have point := G.graph.point_eq_of_coordinate x (height.symm ▸ same)
    rwa [height] at point
  obtain ⟨j, s, on_path⟩ := P.heightGraph_point_on_chain G.graph G.pieces
    (fun j => add_pos (G.positive_steps j).1 (G.positive_steps j).2) h start finish
  let w := (M.geometricParent F covered)^[j.val] z
  let A := centeredPlaneFrame (K.projectedVertex origin) B.place
  have first : A (F.geometricPosition w) = P.vertex j.castSucc := centeredPlaneFrame_apply _ _ _
  have last : A (F.geometricPosition (M.geometricParent F covered w)) = P.vertex j.succ := by
    calc
      _ = B.place (F.geometricPosition (M.geometricParent F covered w) -
          K.projectedVertex origin) := centeredPlaneFrame_apply _ _ _
      _ = P.vertex j.succ := by
        change B.place (F.geometricPosition (M.geometricParent F covered w) -
          K.projectedVertex origin) = B.place
            (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] z) -
              K.projectedVertex origin)
        rw [Function.iterate_succ_apply']
  have leaf_point : A (F.geometricPosition leaf) = P.point j s :=
    (centeredPlaneFrame_apply _ _ _).trans (at_leaf.symm.trans on_path)
  have coordinate_member : A (F.geometricPosition leaf) ∈
      segment ℝ (A (F.geometricPosition w))
        (A (F.geometricPosition (M.geometricParent F covered w))) := by
    rw [leaf_point, first, last]
    exact lineMap_mem_segment ℝ _ _ s.property
  have image : A '' segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w)) =
        segment ℝ (A (F.geometricPosition w))
          (A (F.geometricPosition (M.geometricParent F covered w))) :=
    image_segment ℝ A.toAffineMap _ _
  obtain ⟨y, inside, equal⟩ := image.symm.subset coordinate_member
  have physical_member : F.geometricPosition leaf ∈ segment ℝ (F.geometricPosition w)
      (F.geometricPosition (M.geometricParent F covered w)) := A.injective equal ▸ inside
  have nonroot : w ∉ Q.roots := Q.iterate_lt_distanceToRoot_not_mem z j.isLt
  exact different (M.geometric_leaf_eq_of_mem_ancestor_edge F covered positive small lower
    leaf z w leaf_nonroot childless nonroot ⟨j.val, rfl⟩ physical_member)

end Unfoldings.ConvexCap.SectorForest.SectorTailGraph
