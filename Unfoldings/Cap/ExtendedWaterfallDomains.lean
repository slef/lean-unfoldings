module

public import Unfoldings.Cap.DeepGeometricWaterfall
public import Unfoldings.Cap.ExtendedOutwardForest
public import Unfoldings.Cap.ProjectedDevelopedMap

/-! The constructed waterfall strips lie in the actual fine roof's regular developed domain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C}

namespace RadialCutForest

variable {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem projectedCutSet_subset : K.projectedCutSet R.retain ⊆ cuts := by
  intro x member
  obtain ⟨s, member⟩ := Set.mem_iUnion.mp member
  obtain ⟨cut, on_edge⟩ := Set.mem_iUnion.mp member
  have selected : s ∈ Set.range R.selection.edge := Classical.not_not.mp cut
  obtain ⟨e, rfl⟩ := selected
  exact R.selected_subset e on_edge

end RadialCutForest

namespace SectorForest

variable {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- This constructs regular domains in the actual auxiliary roof mesh. There is no assumed
strip lift or compatible chart selection; both follow from the actual minimal cut development. -/
theorem cornerExtendedOutward_exists_regular_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (cutoff : ℝ) (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆
      interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ i : FiveSector, ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      ∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
        z.re + z.im ∈ Set.Icc 0 cutoff →
          K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
            Q.footprint \ Q.projectedCutSet R.retain := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
      K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier :=
    T.cornerTails_covers_rim inside source_height lower
  refine fun i => ?_
  obtain ⟨P, regular⟩ := M.exists_deep_geometric_sector_waterfall F covered positive small lower
    i cutoff deep
  refine ⟨P, ?_⟩
  intro S cell z member height
  have physical := regular S cell z member height
  constructor
  · rw [L.partition.normalizedCap_footprint L.conforming lower]
    exact interior_subset physical.1
  · exact fun on_cut => physical.2 (R.projectedCutSet_subset on_cut)

end SectorForest
end Unfoldings.ConvexCap
