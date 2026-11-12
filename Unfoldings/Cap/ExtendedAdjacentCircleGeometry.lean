module

public import Unfoldings.Cap.ExtendedRadialWaterfallData
public import Unfoldings.Cap.SharedSeparatorCircleSeparation
public import Unfoldings.Cap.ExtendedLeafCoherence
public import Unfoldings.Cap.RadialWaterfallBankControl
public import Unfoldings.Cap.ExtendedEmptyCircleContinuations

/-! One calibration controls adjacent circles, actual terminal copies, and every roof face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_extended_adjacent_circle_geometry
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
                  (∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
                    p - K.projectedVertex origin ∈ closedFiveSector t i →
                    p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
                    ε * ‖p - K.projectedVertex origin‖ ≤
                      (bankFrame.sectorFrame i (D.projectedPlacement Q f p -
                        D.projectedMap Q (K.projectedVertex origin))).re ∧
                    ε * ‖p - K.projectedVertex origin‖ ≤
                      (bankFrame.sectorFrame i (D.projectedPlacement Q f p -
                        D.projectedMap Q (K.projectedVertex origin))).im) ∧
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
                      (∀ S ∈ P.cells, S.ApproachedPinchesIn
                        (Set.range (fun w : {w : L.partition.pairedComplex.Vertex Set.univ //
                          Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
                          (fiveSectorFrame t positive small i).place
                            (Q.projectedVertex w.val - K.projectedVertex origin))) 0 cutoff) ∧
                      ∃ traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                        R.RadialStripTraceData positive small D calibration i cell.val ε cutoff,
                        (∀ first last : {S : MonotoneStrip // S ∈ P.cells},
                          first.val.upper = last.val.lower → first.val.upper ∈ P.separators →
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (cutoff / 4),
                            radius ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
                              calibration positive small →
                            Disjoint
                              ((traces first).value '' first.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces first).center‖ = radius})
                              ((traces last).value '' last.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces last).center‖ = radius})) ∧
                        ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)),
                            radius ∉ (traces cell).emptyCircleExceptions →
                            (traces cell).value '' cell.val.openSlab 0 cutoff ∩
                              {z | ‖z - (traces cell).center‖ = radius} = ∅ →
                            (cell.val.openSlab 0 cutoff).Nonempty →
                            Nonempty (bankFrame.EmptyCircleContinuation i (traces cell)
                              (cutoff / 4) radius) := by
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
    exists_uniform_extended_vertex_pinched_radial_waterfall.{u, v} t positive small εpositive
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
  have common_margin (i : FiveSector) (z : ℂ)
      (member : z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier)
      (forward : 0 ≤ z.re + z.im) :
      (8 * ε) * ‖z‖ ≤ z.re ∧ (8 * ε) * ‖z‖ ≤ z.im := by
    have coefficient : 8 * ε ≤ μ i := by
      have bound := (min_le_left (μ j / 8) (1 / 8)).trans
        (div_le_div_of_nonneg_right (minimal i) (by norm_num))
      change ε ≤ μ i / 8 at bound
      linarith
    have size := (fiveSectorFrame t positive small i).enclosingStrip_forward_norm_bound
      member forward
    have estimate : (8 * ε) * ‖z‖ ≤ μ i * (z.re + z.im) :=
      (mul_le_mul_of_nonneg_left size (by positivity)).trans
        (mul_le_mul_of_nonneg_right coefficient forward)
    have coordinates := margin i z member forward
    exact ⟨estimate.trans coordinates.1, estimate.trans coordinates.2⟩
  have bank_control := R.waterfallBankControl_of_radial_trace_data positive small D B
    operator_bound (fun i => by
      obtain ⟨P, _, _, _, _, data⟩ := strips i
      exact ⟨P, data⟩)
  have face_geometry : ∀ (i : FiveSector) f p,
      p ∈ (Q.projectedTriangle f).carrier → p - K.projectedVertex origin ∈ closedFiveSector t i →
      p ∈ sectorSweepInterior positive small (K.projectedVertex origin) cutoff →
      ε * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame i (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).re ∧
      ε * ‖p - K.projectedVertex origin‖ ≤
        (B.sectorFrame i (D.projectedPlacement Q f p -
          D.projectedMap Q (K.projectedVertex origin))).im := by
    intro i f p member cone region
    have estimate := bank_control.all_face_quadrant_margin R positive small D B εpositive.le
      common_margin i f member cone region
    have compare : ε * ‖p - K.projectedVertex origin‖ ≤
        (8 * ε - 2 * ε) * ‖p - K.projectedVertex origin‖ := by
      have product := mul_nonneg εpositive.le (norm_nonneg (p - K.projectedVertex origin))
      nlinarith
    exact ⟨compare.trans estimate.1, compare.trans estimate.2⟩
  refine ⟨B, operator_bound, face_geometry, ?_⟩
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, vertex_pinches, cells⟩ := strips i
  let traces := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    Classical.choice (cells cell.val cell.property)
  refine ⟨P, provenance, represented, coordinates, vertex_pinches, traces, ?_, ?_⟩
  · intro first last wall separator radius radius_bounds outside
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
  · intro cell radius radius_bounds outside empty nonempty
    exact M.cornerExtendedOutward_empty_circle_continuation positive small T internal source_height
      lower conforming height cutoff deep ⟨εpositive, εsmall⟩ D B face_geometry budget i cell.val
      (traces cell) (vertex_pinches cell.val cell.property) radius radius_bounds outside empty
      nonempty

end Unfoldings.ConvexCap
