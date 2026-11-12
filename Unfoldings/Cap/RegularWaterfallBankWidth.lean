module

public import Unfoldings.Cap.ClosedSectorStrip
public import Unfoldings.Cap.RegularWaterfallWidth

/-! Regular actual bank width follows from deep clipping and the constructed subdivision. -/

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

theorem regular_waterfall_bank_width (T : K.ClipSpatialTriangles Z) (i : FiveSector)
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (S : MonotoneStrip) (cell : S ∈ P.cells) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (pinches : S.RecoverablePinchesIn
      (insert 0 (Set.range (fun leaf : M.GeometricSectorLeaf F covered positive small lower i =>
        leaf.point))) 0 cutoff) :
    let B := fiveSectorFrame t positive small i
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ {z : ℂ}, z ∈ S.carrier → z.re + z.im ∈ Set.Icc 0 cutoff →
      (∀ f j, K.projectedVertex origin + B.place.symm z ≠ (Q.projectedTriangle f).vertex j) →
      ∀ {k : ℝ}, k ∈ Set.Icc (z.re + z.im) cutoff →
        S.lower.coordinate k < S.upper.coordinate k →
        S.lower.coordinate (z.re + z.im) < S.upper.coordinate (z.re + z.im) := by
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun {z} member slab regular {k} active width => ?_
  have bounds := P.cell_bounds cell (z.re + z.im)
  have root : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier :=
    ⟨bounds.1.trans member.1, member.2.trans bounds.2⟩
  have physical := deep (closed_sector_strip_slab_mem_closedBall positive small i
    (K.projectedVertex origin) root slab)
  exact M.regular_waterfall_width F covered positive small lower T i S cutoff pinches
    member slab physical regular active width

end Unfoldings.ConvexCap.SectorForest
