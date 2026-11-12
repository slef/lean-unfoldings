module

public import Unfoldings.Cap.GeometricTailLocalEdge
public import Unfoldings.Cap.GeometricSectorBankPoints
public import Unfoldings.Geometry.AffineGraphPinches

/-! Actual tail graphs and exterior rays are locally affine away from geometric vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Filter Topology

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_affineAt {h : ℝ} (positive : 0 < h) :
    B.enclosingStrip.lower.AffineAt h ∧ B.enclosingStrip.upper.AffineAt h := by
  constructor
  · refine ⟨0, B.enclosingStrip.lower.coordinate 1, ?_⟩
    exact Filter.mem_of_superset (Ioi_mem_nhds positive) (fun k after => by
      change B.enclosingStrip.lower.coordinate k = 0 + B.enclosingStrip.lower.coordinate 1 * k
      rw [zero_add]
      exact (B.enclosingStrip_coordinate_homogeneous after.le).1)
  · refine ⟨0, B.enclosingStrip.upper.coordinate 1, ?_⟩
    exact Filter.mem_of_superset (Ioi_mem_nhds positive) (fun k after => by
      change B.enclosingStrip.upper.coordinate k = 0 + B.enclosingStrip.upper.coordinate 1 * k
      rw [zero_add]
      exact (B.enclosingStrip_coordinate_homogeneous after.le).2)

end AcuteWedgeFrame

namespace ConvexCap.SectorForest.SectorTailGraph

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  {w : F.GeometricVertex}

/-- The only possible corners of an actual covered tail lie at geometric vertices. -/
theorem affineAt_of_ne_vertices (A : M.SectorTailGraph F covered positive small lower i w)
    {h : ℝ} (start : M.geometricTailStartHeight F covered positive small lower i w < h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w)
    (not_vertex : ∀ v : F.GeometricVertex, A.graph.point h ≠
      (fiveSectorFrame t positive small i).place
        (F.geometricPosition v - K.projectedVertex origin)) :
    A.graph.AffineAt h := by
  let N := M.sectorHeightNetwork F covered positive small lower i
  let a := M.geometricTailStartHeight F covered positive small lower i w
  let b := (h + M.geometricTailEndHeight F covered positive small lower i w) / 2
  have finish_b : b < M.geometricTailEndHeight F covered positive small lower i w := by
    dsimp only [b]
    linarith
  have within : h ∈ Set.Ioo a b := ⟨start, by dsimp only [b]; linarith⟩
  have cover : ∀ k ∈ Set.Icc a b, A.graph.point k ∈ N.carrier :=
    fun k member => A.covered k member.1 (member.2.trans_lt finish_b)
  obtain ⟨e, member⟩ := Set.mem_iUnion.mp (A.covered h start.le finish)
  have not_last (j : M.GeometricSectorEdge F covered positive small lower i) :
      A.graph.point h ≠ N.last j := by
    have endpoint : N.last j = (fiveSectorFrame t positive small i).place
        (F.geometricPosition (M.geometricParent F covered j.val) - K.projectedVertex origin) :=
      centeredPlaneFrame_apply _ _ _
    rw [endpoint]
    exact not_vertex _
  obtain ⟨c, d, bounds, equal⟩ := N.graph_locally_eq_through A.graph cover within e member not_last
    (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).1
    (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).2
  have affine : (MonotoneHeightGraph.through (N.first e) (N.last e)
      (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).1
      (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).2
      (sub_pos.mpr (N.ascending e))).AffineAt h :=
    MonotoneHeightGraph.affine_affineAt _ _ _ _ _ h
  exact affine.congr_on_Ioo equal bounds

end ConvexCap.SectorForest.SectorTailGraph
end Unfoldings
