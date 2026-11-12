module

public import Unfoldings.Cap.GeometricTailCoalescence
public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Cap.ExtendedLeafCoherence
public import Unfoldings.Geometry.HeightNetworkLocalGraph

/-! Actual regular tail points avoid network vertices and retain a local physical edge graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

include M covered positive small in
theorem regular_meshed_point_ne_geometric_vertex (T : K.ClipSpatialTriangles Z) :
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ p ∈ interior (K.clipFootprint Z),
      (∀ f j, p ≠ (Q.projectedTriangle f).vertex j) →
      ∀ w : F.GeometricVertex, p ≠ F.geometricPosition w := by
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun p inside regular w same => ?_
  by_cases root : w ∈ (M.geometricParents F covered positive small lower).roots
  · obtain ⟨c, rfl⟩ := root
    change p = (F.componentTail c).tip at same
    exact (F.componentTail c).boundary.2 (same ▸ inside)
  · obtain ⟨v, position, _⟩ := M.meshed_geometric_nonroot_vertex F covered positive small
      lower T w root
    change Q.projectedVertex v = F.geometricPosition w at position
    obtain ⟨⟨f, j⟩, rfl⟩ := L.partition.pairedComplex.vertexOfCorner_surjective Set.univ v
    exact regular f j (same.trans position.symm)

theorem sectorHeightNetwork_coordinate_steps (i : FiveSector)
    (e : M.GeometricSectorEdge F covered positive small lower i) :
    let N := M.sectorHeightNetwork F covered positive small lower i
    (N.first e).re ≤ (N.last e).re ∧ (N.first e).im ≤ (N.last e).im := by
  let B := fiveSectorFrame t positive small i
  let N := M.sectorHeightNetwork F covered positive small lower i
  have movement : N.last e - N.first e =
      B.place (F.geometricPosition (M.geometricParent F covered e.val) -
        F.geometricPosition e.val) := by
    change centeredPlaneFrame _ _ _ - centeredPlaneFrame _ _ _ = _
    rw [centeredPlaneFrame_apply, centeredPlaneFrame_apply, ← B.place.map_sub]
    congr 1
    abel
  have quadrant := B.quadrant_nonneg e.property.2
  rw [← movement, Complex.sub_re, Complex.sub_im] at quadrant
  exact ⟨sub_nonneg.mp quadrant.1, sub_nonneg.mp quadrant.2⟩

namespace SectorTailGraph

variable {M F covered positive small lower} {i : FiveSector} {w : F.GeometricVertex}

/-- Local straight-edge agreement follows from the actual finite network and roof mesh.
Neither local bank matching nor a safe-cut hypothesis is supplied. -/
theorem locally_eq_edge (A : M.SectorTailGraph F covered positive small lower i w)
    (T : K.ClipSpatialTriangles Z) (h : ℝ)
    (start : M.geometricTailStartHeight F covered positive small lower i w < h)
    (finish : h < M.geometricTailEndHeight F covered positive small lower i w) :
    let B := fiveSectorFrame t positive small i
    let N := M.sectorHeightNetwork F covered positive small lower i
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let p := K.projectedVertex origin + B.place.symm (A.graph.point h)
    p ∈ interior (K.clipFootprint Z) →
      (∀ f j, p ≠ (Q.projectedTriangle f).vertex j) →
      ∃ e : M.GeometricSectorEdge F covered positive small lower i, ∃ c d,
        h ∈ Set.Ioo c d ∧ Set.EqOn A.graph.coordinate
          (MonotoneHeightGraph.through (N.first e) (N.last e)
            (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).1
            (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).2
            (sub_pos.mpr (N.ascending e))).coordinate (Set.Ioo c d) := by
  let B := fiveSectorFrame t positive small i
  let N := M.sectorHeightNetwork F covered positive small lower i
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let p := K.projectedVertex origin + B.place.symm (A.graph.point h)
  refine fun inside regular => ?_
  have avoid := M.regular_meshed_point_ne_geometric_vertex F covered positive small lower T
    p inside regular
  have not_vertex (e : M.GeometricSectorEdge F covered positive small lower i) :
      A.graph.point h ≠ N.last e := by
    intro same
    have last : N.last e = B.place (F.geometricPosition (M.geometricParent F covered e.val) -
        K.projectedVertex origin) := centeredPlaneFrame_apply _ _ _
    rw [last] at same
    apply avoid (M.geometricParent F covered e.val)
    dsimp only [p]
    rw [same, B.place.symm_apply_apply]
    abel
  let a := M.geometricTailStartHeight F covered positive small lower i w
  let b := (h + M.geometricTailEndHeight F covered positive small lower i w) / 2
  have finish_b : b < M.geometricTailEndHeight F covered positive small lower i w := by
    dsimp only [b]
    linarith
  have within : h ∈ Set.Ioo a b := ⟨start, by dsimp only [b]; linarith⟩
  have cover : ∀ k ∈ Set.Icc a b, A.graph.point k ∈ N.carrier :=
    fun k member => A.covered k member.1 (member.2.trans_lt finish_b)
  obtain ⟨e, on_edge⟩ := Set.mem_iUnion.mp (A.covered h start.le finish)
  exact ⟨e, N.graph_locally_eq_through A.graph cover within e on_edge not_vertex
    (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).1
    (M.sectorHeightNetwork_coordinate_steps F covered positive small lower i e).2⟩

end SectorTailGraph
end Unfoldings.ConvexCap.SectorForest
