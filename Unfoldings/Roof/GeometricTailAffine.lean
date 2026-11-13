module

public import Unfoldings.Cap.GeometricTailAffine

public import Unfoldings.Roof.GeometricTailLocalEdge
public import Unfoldings.Cap.GeometricSectorBankPoints
public import Unfoldings.Geometry.AffineGraphPinches

/-! Actual tail graphs and exterior rays are locally affine away from geometric vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexRoof.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outer : Set Plane} {F : K.SkirtTailFamily outer (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  {w : F.GeometricVertex}

/-- The only possible corners of an actual covered tail lie at geometric vertices. -/
theorem affineAt_of_ne_vertices (A : M.SectorTailGraph F covered positive small i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small i w < h)
    (finish : h < M.geometricTailEndHeight F covered positive small i w)
    (not_vertex : ∀ v : F.GeometricVertex, A.graph.point h ≠
      (fiveSectorFrame t positive small i).place
        (F.geometricPosition v - origin)) :
    A.graph.AffineAt h := by
  let N := M.sectorHeightNetwork F covered positive small i
  let a := M.geometricTailStartHeight F covered positive small i w
  let b := (h + M.geometricTailEndHeight F covered positive small i w) / 2
  have finish_b : b < M.geometricTailEndHeight F covered positive small i w := by
    dsimp only [b]
    linarith
  have within : h ∈ Set.Ioo a b := ⟨start, by dsimp only [b]; linarith⟩
  have cover : ∀ k ∈ Set.Icc a b, A.graph.point k ∈ N.carrier :=
    fun k member => A.covered k member.1 (member.2.trans_lt finish_b)
  obtain ⟨e, member⟩ := Set.mem_iUnion.mp (A.covered h start.le finish)
  have not_last (j : M.GeometricSectorEdge F covered positive small i) :
      A.graph.point h ≠ N.last j := by
    have endpoint : N.last j = (fiveSectorFrame t positive small i).place
        (F.geometricPosition (M.geometricParent F covered j.val) - origin) :=
      centeredPlaneFrame_apply _ _ _
    rw [endpoint]
    exact not_vertex _
  obtain ⟨c, d, bounds, equal⟩ := N.graph_locally_eq_through A.graph cover within e member not_last
    (M.sectorHeightNetwork_coordinate_steps F covered positive small i e).1
    (M.sectorHeightNetwork_coordinate_steps F covered positive small i e).2
  have affine : (MonotoneHeightGraph.through (N.first e) (N.last e)
      (M.sectorHeightNetwork_coordinate_steps F covered positive small i e).1
      (M.sectorHeightNetwork_coordinate_steps F covered positive small i e).2
      (sub_pos.mpr (N.ascending e))).AffineAt h :=
    MonotoneHeightGraph.affine_affineAt _ _ _ _ _ h
  exact affine.congr_on_Ioo equal bounds

end ConvexRoof.SectorForest.SectorTailGraph
end Unfoldings
