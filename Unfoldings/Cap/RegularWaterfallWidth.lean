module

public import Unfoldings.Cap.GeometricTailLocalEdge
public import Unfoldings.Geometry.RecoverableStripRegularWidth

/-! Actual regular bank points avoid the waterfall pinch set and have positive strip width. -/

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

theorem regular_point_not_waterfall_pinches (T : K.ClipSpatialTriangles Z) (i : FiveSector) :
    let B := fiveSectorFrame t positive small i
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ z : ℂ, K.projectedVertex origin + B.place.symm z ∈ interior (K.clipFootprint Z) →
      (∀ f j, K.projectedVertex origin + B.place.symm z ≠ (Q.projectedTriangle f).vertex j) →
      z ∉ insert 0 (Set.range (fun leaf : M.GeometricSectorLeaf F covered positive small lower i =>
        leaf.point)) := by
  let B := fiveSectorFrame t positive small i
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun z inside regular member => ?_
  have avoid := M.regular_meshed_point_ne_geometric_vertex F covered positive small lower T
    (K.projectedVertex origin + B.place.symm z) inside regular
  rcases member with source | leaf
  · apply avoid (Sum.inl origin)
    rw [source, map_zero, add_zero]
    rfl
  · obtain ⟨leaf, rfl⟩ := leaf
    apply avoid leaf.val
    change K.projectedVertex origin + B.place.symm
      (B.place (F.geometricPosition leaf.val - K.projectedVertex origin)) = _
    rw [B.place.symm_apply_apply]
    abel

theorem regular_waterfall_width (T : K.ClipSpatialTriangles Z) (i : FiveSector)
    (S : MonotoneStrip) (cutoff : ℝ)
    (pinches : S.RecoverablePinchesIn
      (insert 0 (Set.range (fun leaf : M.GeometricSectorLeaf F covered positive small lower i =>
        leaf.point))) 0 cutoff) :
    let B := fiveSectorFrame t positive small i
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ {z : ℂ}, z ∈ S.carrier → z.re + z.im ∈ Set.Icc 0 cutoff →
      K.projectedVertex origin + B.place.symm z ∈ interior (K.clipFootprint Z) →
      (∀ f j, K.projectedVertex origin + B.place.symm z ≠ (Q.projectedTriangle f).vertex j) →
      ∀ {k : ℝ}, k ∈ Set.Icc (z.re + z.im) cutoff →
        S.lower.coordinate k < S.upper.coordinate k →
        S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im) := by
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun {z} member slab inside regular {k} active width => ?_
  exact S.width_pos_of_recoverable_regular pinches member slab active width
    (M.regular_point_not_waterfall_pinches F covered positive small lower T i z inside regular)

end Unfoldings.ConvexCap.SectorForest
