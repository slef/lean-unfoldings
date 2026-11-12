module

public import Unfoldings.Cap.ExtendedRadialWaterfallData
public import Unfoldings.Cap.SharedSeparatorCircleSeparation
public import Unfoldings.Cap.ExtendedLeafCoherence

/-! Uniformly construct actual adjacent-strip circle separation before both meshes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- The same constructed subdivision and radial trace family have disjoint adjacent
source-circle slices, apart from one proved finite vertex-radius set. Tilt and numerical
thresholds precede both meshes. All shared-prefix and actual tail hypotheses are derived. -/
theorem exists_uniform_extended_adjacent_circle_separation
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let covered := T.cornerTails_covers_rim inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                L.partition.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      (∀ G ∈ P.separators,
                        ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
                          leaf.point.re + leaf.point.im ≤ cutoff ∧
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
                        leaf.point.re + leaf.point.im ≤ cutoff →
                          ∃ G ∈ P.separators,
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
                        S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
                      ∃ traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                        R.RadialStripTraceData positive small D calibration i cell.val ε cutoff,
                        ∀ first last : {S : MonotoneStrip // S ∈ P.cells},
                          first.val.upper = last.val.lower → first.val.upper ∈ P.separators →
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (cutoff / 4),
                            radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
                              calibration positive small →
                            Disjoint
                              ((traces first).value '' first.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces first).center‖ = radius})
                              ((traces last).value '' last.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces last).center‖ = radius}) := by
  classical
  have margins := fun i : FiveSector =>
    (fiveSectorFrame t positive small i).exists_enclosingStrip_coordinate_margin
  choose μ μpositive margin using margins
  obtain ⟨j, minimal⟩ := Finite.exists_min μ
  let ε := min (μ j / 8) (1 / 8)
  have εpositive : 0 < ε := lt_min (div_pos (μpositive j) (by norm_num)) (by norm_num)
  have εsmall : ε ≤ 1 / 8 := min_le_right _ _
  have numerical (i : FiveSector) : ε * (1 + ε) < μ i - ε := by
    have bound : ε ≤ μ i / 8 := (min_le_left _ _).trans
      (div_le_div_of_nonneg_right (minimal i) (by norm_num))
    nlinarith [εpositive]
  have close_margin (i : FiveSector) : ε < μ i := by
    nlinarith [numerical i, sq_nonneg ε]
  obtain ⟨φ, bounds, normal, construct⟩ :=
    exists_uniform_extended_radial_waterfall_data.{u, v} t positive small εpositive
  refine ⟨ε, ⟨εpositive, εsmall⟩, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let network := M.cornerExtendedOutwardForest positive small T internal source_height lower
  let R := network.val
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  have leaves := M.cornerExtended_geometric_leaf_coherent positive small T internal source_height
    lower conforming height
  have curvature :=
    M.extended_cut_curvature_covered T internal source_height lower conforming height
  obtain ⟨budget, frames⟩ :=
    construct K tilt M internal source_height lower T conforming cutoff deep
  refine ⟨budget, fun D => ?_⟩
  obtain ⟨B, operator_bound, strips⟩ := frames D
  let calibration := R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference
  refine ⟨B, operator_bound, ?_⟩
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, cells⟩ := strips i
  let traces := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    Classical.choice (cells cell.val cell.property)
  refine ⟨P, provenance, represented, coordinates, traces, ?_⟩
  intro first last wall separator radius radius_bounds outside
  let data := traces first
  let other := traces last
  have cell_margin (S : MonotoneStrip) (cell : S ∈ P.cells) :
      ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
        μ i * (z.re + z.im) ≤ z.re ∧ μ i * (z.re + z.im) ≤ z.im := by
    intro z member forward
    exact margin i z ((P.cover z).mpr ⟨S, cell, member⟩) forward
  have cutoff_positive : 0 < cutoff := by linarith [radius_bounds.1, radius_bounds.2]
  have far : radius < (1 / 2 - ε) * cutoff := radius_bounds.2.trans_le (by
    have coefficient : (1 : ℝ) / 4 ≤ 1 / 2 - ε := by linarith [εsmall]
    have product := mul_le_mul_of_nonneg_right coefficient cutoff_positive.le
    linarith)
  by_cases first_meets : (data.value '' first.val.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius}).Nonempty
  · by_cases last_meets : (other.value '' last.val.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius}).Nonempty
    · obtain ⟨first_slice⟩ := data.circle_slice (close_margin i)
        (cell_margin first.val first.property) radius_bounds.1 far first_meets
      obtain ⟨last_slice⟩ := other.circle_slice (close_margin i)
        (cell_margin last.val last.property) radius_bounds.1 far last_meets
      obtain ⟨leaf, active, completion⟩ := provenance first.val.upper separator
      obtain ⟨w, position, coherent⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
      have coherent_minimal : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val) :=
        coherent (R.completedDevelopment D)
      exact leaf.circle_shared_separator_slices_disjoint R network.property w position
        (L.partition.normalizedCap_footprint L.conforming lower) deep P represented D B data other
        cells first.property last.property separator rfl wall.symm active completion
        coherent_minimal
        εpositive.le (εsmall.trans_lt (by norm_num)) (numerical i)
        (fun f z => operator_bound _ f z) (cell_margin first.val first.property)
        (cell_margin last.val last.property) curvature budget radius_bounds.1 far outside
        first_slice last_slice
    · have empty := Set.not_nonempty_iff_eq_empty.mp last_meets
      rw [empty]
      exact Set.disjoint_empty _
  · have empty := Set.not_nonempty_iff_eq_empty.mp first_meets
    rw [empty]
    exact Set.empty_disjoint _

end Unfoldings.ConvexCap
