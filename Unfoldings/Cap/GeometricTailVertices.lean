module

public import Unfoldings.Cap.GeometricTailCoalescence
public import Unfoldings.Cap.GeometricCutIncidence

/-! A geometric vertex on an actual tail is an ancestor in that same cut component. -/

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
  {w z : F.GeometricVertex}

theorem vertex_ancestor_of_point (G : M.SectorTailGraph F covered positive small lower i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small lower i w ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w)
    (at_vertex : G.graph.point h = (fiveSectorFrame t positive small i).place
      (F.geometricPosition z - K.projectedVertex origin)) :
    (M.geometricParents F covered positive small lower).Ancestor w z := by
  let B := fiveSectorFrame t positive small i
  let P := M.geometricRootPath F covered positive small lower B.place w
  let Q := M.geometricParents F covered positive small lower
  obtain ⟨j, s, on_path⟩ := P.heightGraph_point_on_chain G.graph G.pieces
    (fun j => add_pos (G.positive_steps j).1 (G.positive_steps j).2) h start finish
  let v := (M.geometricParent F covered)^[j.val] w
  let A := centeredPlaneFrame (K.projectedVertex origin) B.place
  have first : A (F.geometricPosition v) = P.vertex j.castSucc := centeredPlaneFrame_apply _ _ _
  have last : A (F.geometricPosition (M.geometricParent F covered v)) = P.vertex j.succ := by
    calc
      _ = B.place (F.geometricPosition (M.geometricParent F covered v) -
          K.projectedVertex origin) := centeredPlaneFrame_apply _ _ _
      _ = P.vertex j.succ := by
        change B.place (F.geometricPosition (M.geometricParent F covered v) -
          K.projectedVertex origin) = B.place
            (F.geometricPosition ((M.geometricParent F covered)^[j.val + 1] w) -
              K.projectedVertex origin)
        rw [Function.iterate_succ_apply']
  have position : A (F.geometricPosition z) = P.point j s :=
    (centeredPlaneFrame_apply _ _ _).trans (at_vertex.symm.trans on_path)
  have coordinate_member : A (F.geometricPosition z) ∈
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
  have physical : F.geometricPosition z ∈ segment ℝ (F.geometricPosition v)
      (F.geometricPosition (M.geometricParent F covered v)) := A.injective equal ▸ inside
  have nonroot : v ∉ Q.roots := Q.iterate_lt_distanceToRoot_not_mem w j.isLt
  rcases M.geometric_vertex_on_parent_endpoint F covered positive small lower z v nonroot physical
      with at_first | at_last
  · exact ⟨j.val, at_first.symm⟩
  · exact ⟨j.val + 1, by
      change (M.geometricParent F covered)^[j.val + 1] w = z
      rw [Function.iterate_succ_apply']
      exact at_last.symm⟩

theorem vertex_component_of_point (G : M.SectorTailGraph F covered positive small lower i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small lower i w ≤ h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w)
    (at_vertex : G.graph.point h = (fiveSectorFrame t positive small i).place
      (F.geometricPosition z - K.projectedVertex origin)) :
    M.geometricComponent F covered z = M.geometricComponent F covered w := by
  obtain ⟨n, equal⟩ := G.vertex_ancestor_of_point start finish at_vertex
  rw [← equal]
  exact M.geometricComponent_iterate F covered w n

end Unfoldings.ConvexCap.SectorForest.SectorTailGraph
