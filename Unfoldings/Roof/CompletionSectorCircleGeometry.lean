module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionRadialWaterfallData
public import Unfoldings.Roof.SharedSeparatorCircleSeparation
public import Unfoldings.Roof.CompletionLeafCoherence
public import Unfoldings.Cap.RadialWaterfallBankControl
public import Unfoldings.Roof.CompletionEmptyCircleContinuations
public import Unfoldings.Roof.EmptyStripCircleSeparation
public import Unfoldings.Roof.WaterfallCircleSurvivors

/-! Uniform separation of all actual strip-circle images within each waterfall sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

theorem exists_uniform_completion_sector_circle_geometry
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {origin : Plane} (M : K.SectorForest t origin),
          ∀ {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
            (T : K.CompletionMesh φ region extra),
                ∀ cutoff : ℝ, Metric.closedBall origin cutoff ⊆
                  interior (T.domain) →
                let inside := M.inside
                let F := T.cornerTails inside
                let covered := T.cornerTails_covers_rim inside
                let L := T.radialMesh M.inside
                let Q := L.cap
                letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
                let R := (M.completionOutwardForest T positive small).val
                L.mesh.toTriangulation.pairedComplex.totalInteriorAngularDefect Set.univ < Real.pi ∧
                ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
                  ∃ bankFrame : R.FiveSectorFrameData positive small (R.completedDevelopment D),
                  let calibration := R.calibratedFrame (R.completedDevelopment D)
                    bankFrame.anchor bankFrame.reference
                  (∀ (frame : Plane ≃ₗᵢ[ℝ] ℂ) f z,
                    ‖(D.coordinatePlacement Q calibration frame f).linear z - z‖ ≤ ε * ‖z‖) ∧
                  (∀ (i : FiveSector) f p, p ∈ (Q.projectedTriangle f).carrier →
                    p - origin ∈ closedFiveSector t i →
                    p ∈ sectorSweepInterior positive small origin cutoff →
                    ε * ‖p - origin‖ ≤
                      (bankFrame.sectorFrame i (D.projectedPlacement Q f p -
                        D.projectedMap Q origin)).re ∧
                    ε * ‖p - origin‖ ≤
                      (bankFrame.sectorFrame i (D.projectedPlacement Q f p -
                        D.projectedMap Q origin)).im) ∧
                  ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
                      (∀ G ∈ P.separators,
                        ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
                          leaf.point.re + leaf.point.im ≤ cutoff ∧
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ leaf : M.GeometricSectorLeaf F covered positive small i,
                        leaf.point.re + leaf.point.im ≤ cutoff →
                          ∃ G ∈ P.separators,
                            MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff G) ∧
                      (∀ S ∈ P.cells, S.lower.StrictCoordinatesOn (Set.Icc 0 cutoff) ∧
                        S.upper.StrictCoordinatesOn (Set.Icc 0 cutoff)) ∧
                      (∀ S ∈ P.cells, S.TerminalTailsFrom
                        (fun leaf : M.GeometricSectorLeaf F covered positive small i =>
                          leaf.point) (fun leaf => leaf.tailGraph.graph) cutoff) ∧
                      (∀ S ∈ P.cells, S.ApproachedPinchesIn
                        (Set.range (fun w :
                          {w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ //
                          Q.projectedVertex w ∈ M.extendedGeometricCuts F} =>
                          (fiveSectorFrame t positive small i).place
                            (Q.projectedVertex w.val - origin))) 0 cutoff) ∧
                      ∃ traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                        R.RadialStripTraceData positive small D calibration i cell.val ε cutoff,
                        (∀ first last : {S : MonotoneStrip // S ∈ P.cells},
                          first.val.upper = last.val.lower → first.val.upper ∈ P.separators →
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (cutoff / 4),
                            radius ∉ D.fiveSectorVertexRadii Q origin
                              calibration positive small →
                            Disjoint
                              ((traces first).value '' first.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces first).center‖ = radius})
                              ((traces last).value '' last.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces last).center‖ = radius})) ∧
                        (∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)),
                            radius ∉ (traces cell).emptyCircleExceptions →
                            (traces cell).value '' cell.val.openSlab 0 cutoff ∩
                              {z | ‖z - (traces cell).center‖ = radius} = ∅ →
                            (cell.val.openSlab 0 cutoff).Nonempty →
                            Nonempty (bankFrame.EmptyCircleContinuation i (traces cell)
                              (cutoff / 4) radius)) ∧
                        (∀ first middle last : {S : MonotoneStrip // S ∈ P.cells},
                          first.val.upper = middle.val.lower →
                          last.val.lower = middle.val.upper →
                          middle.val.lower ∈ P.separators → middle.val.upper ∈ P.separators →
                          ∀ radius ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)),
                            radius ∉ D.fiveSectorVertexRadii Q origin
                              calibration positive small →
                            radius ∉ (traces middle).emptyCircleExceptions →
                            (traces middle).value '' middle.val.openSlab 0 cutoff ∩
                              {z | ‖z - (traces middle).center‖ = radius} = ∅ →
                            (middle.val.openSlab 0 cutoff).Nonempty →
                            Disjoint
                              ((traces first).value '' first.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces first).center‖ = radius})
                              ((traces last).value '' last.val.openSlab 0 cutoff ∩
                                {z | ‖z - (traces last).center‖ = radius})) ∧
                        ∀ radius ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)),
                          radius ∉ D.fiveSectorVertexRadii Q origin
                            calibration positive small →
                          (∀ cell : {S : MonotoneStrip // S ∈ P.cells},
                            radius ∉ (traces cell).emptyCircleExceptions) →
                          P.cells.attach.Pairwise (fun first last => Disjoint
                            ((traces first).value '' first.val.openSlab 0 cutoff ∩
                              {z | ‖z - (traces first).center‖ = radius})
                            ((traces last).value '' last.val.openSlab 0 cutoff ∩
                              {z | ‖z - (traces last).center‖ = radius})) := by
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
    exists_uniform_completion_terminal_radial_waterfall.{u, v} t positive small εpositive
  refine ⟨ε, ⟨εpositive, εsmall⟩, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M region J extra T cutoff deep
  let inside := M.inside
  let F := T.cornerTails inside
  let covered := T.cornerTails_covers_rim inside
  let L := T.radialMesh M.inside
  let Q := L.cap
  let := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
  let network := M.completionOutwardForest T positive small
  let R := network.val
  have height : ∀ i, (3 : ℝ) / 4 ≤ (T.supportPlanes i).normal 2 := fun i =>
    normal.trans (K.completionPlanes_tilt bounds.1 bounds.2 tilt T.tentHeight i)
  have leaves := M.completion_geometric_leaf_coherent T positive small height
  have curvature :=
    M.radialMesh_curvature_covered T height
  obtain ⟨budget, frames⟩ :=
    construct K tilt M T cutoff deep
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
      obtain ⟨P, _, _, _, _, _, data⟩ := strips i
      exact ⟨P, data⟩)
  have face_geometry : ∀ (i : FiveSector) f p,
      p ∈ (Q.projectedTriangle f).carrier → p - origin ∈ closedFiveSector t i →
      p ∈ sectorSweepInterior positive small origin cutoff →
      ε * ‖p - origin‖ ≤
        (B.sectorFrame i (D.projectedPlacement Q f p -
          D.projectedMap Q origin)).re ∧
      ε * ‖p - origin‖ ≤
        (B.sectorFrame i (D.projectedPlacement Q f p -
          D.projectedMap Q origin)).im := by
    intro i f p member cone region
    have estimate := bank_control.all_face_quadrant_margin R positive small D B εpositive.le
      common_margin i f member cone region
    have compare : ε * ‖p - origin‖ ≤
        (8 * ε - 2 * ε) * ‖p - origin‖ := by
      have product := mul_nonneg εpositive.le (norm_nonneg (p - origin))
      nlinarith
    exact ⟨compare.trans estimate.1, compare.trans estimate.2⟩
  refine ⟨B, operator_bound, face_geometry, ?_⟩
  refine fun i => ?_
  obtain ⟨P, provenance, represented, coordinates, terminal_tails, vertex_pinches, cells⟩ :=
    strips i
  let traces := fun cell : {S : MonotoneStrip // S ∈ P.cells} =>
    Classical.choice (cells cell.val cell.property)
  refine ⟨P, provenance, represented, coordinates, terminal_tails, vertex_pinches,
    traces, ?_, ?_, ?_, ?_⟩
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
          (L.cap_footprint) deep P represented D B data other
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
    exact M.completionOutward_empty_circle_continuation positive small T
        height cutoff deep ⟨εpositive, εsmall⟩ D B face_geometry budget i cell.val
      (traces cell) (vertex_pinches cell.val cell.property) radius radius_bounds outside empty
      nonempty
  · intro first middle last first_wall last_wall first_separator last_separator radius
      radius_bounds outside outside_middle empty nonempty
    have cutoff_positive : 0 < cutoff := by
      have product : 0 < ε * (cutoff / 4) := radius_bounds.1.trans radius_bounds.2
      have quarter_positive : 0 < cutoff / 4 :=
        (mul_pos_iff_of_pos_left εpositive).mp product
      linarith
    have far : radius < (1 / 2 - ε) * cutoff := radius_bounds.2.trans_le (by
      nlinarith [mul_nonneg (by linarith [εsmall] : 0 ≤ 1 / 2 - 5 * ε / 4)
        cutoff_positive.le])
    have cell_margin (S : MonotoneStrip) (cell : S ∈ P.cells) :
        ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
          μ i * (z.re + z.im) ≤ z.re ∧ μ i * (z.re + z.im) ≤ z.im := by
      intro z member forward
      exact margin i z ((P.cover z).mpr ⟨S, cell, member⟩) forward
    by_cases first_meets : ((traces first).value '' first.val.openSlab 0 cutoff ∩
        {z | ‖z - (traces first).center‖ = radius}).Nonempty
    · by_cases last_meets : ((traces last).value '' last.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces last).center‖ = radius}).Nonempty
      · obtain ⟨first_slice⟩ := (traces first).circle_slice (close_margin i)
          (cell_margin first.val first.property) radius_bounds.1 far first_meets
        obtain ⟨last_slice⟩ := (traces last).circle_slice (close_margin i)
          (cell_margin last.val last.property) radius_bounds.1 far last_meets
        obtain ⟨continuation⟩ := M.completionOutward_empty_circle_continuation positive small T
              height cutoff deep ⟨εpositive, εsmall⟩ D B
          face_geometry budget i middle.val (traces middle)
          (vertex_pinches middle.val middle.property) radius radius_bounds outside_middle empty
          nonempty
        have realization (H : MonotoneHeightGraph) (separator : H ∈ P.separators) :
            ∃ leaf : M.GeometricSectorLeaf F covered positive small i,
              ∃ w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
                Q.projectedVertex w = F.geometricPosition leaf.val ∧
                  leaf.point.re + leaf.point.im ≤ cutoff ∧
                  D.ProjectedCoherentAt Q (F.geometricPosition leaf.val) ∧
                  MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H := by
          obtain ⟨leaf, active, completion⟩ := provenance H separator
          obtain ⟨w, position, coherent⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
          exact ⟨leaf, w, position, active, coherent (R.completedDevelopment D), completion⟩
        exact SectorForest.circle_slices_disjoint_across_empty_strip R network.property D B
          (traces first) (traces last) (traces middle)
          (terminal_tails middle.val middle.property) continuation
          (L.cap_footprint) deep εpositive.le
          (εsmall.trans_lt (by norm_num)) (numerical i) (fun f z => operator_bound _ f z)
          (cell_margin first.val first.property) (cell_margin last.val last.property)
          curvature budget radius_bounds.1 far outside first_slice last_slice first_wall last_wall
          P represented (fun S member => ⟨traces ⟨S, member⟩⟩) first.property last.property
          middle.property (vertex_pinches middle.val middle.property) outside_middle empty
          first_separator last_separator (realization _ first_separator)
          (realization _ last_separator)
      · have empty_last := Set.not_nonempty_iff_eq_empty.mp last_meets
        rw [empty_last]
        exact Set.disjoint_empty _
    · have empty_first := Set.not_nonempty_iff_eq_empty.mp first_meets
      rw [empty_first]
      exact Set.empty_disjoint _
  · intro radius radius_bounds outside outside_empty
    have cutoff_positive : 0 < cutoff := by
      have product : 0 < ε * (cutoff / 4) := radius_bounds.1.trans radius_bounds.2
      have quarter_positive : 0 < cutoff / 4 :=
        (mul_pos_iff_of_pos_left εpositive).mp product
      linarith
    have far : radius < (1 / 2 - ε) * cutoff := radius_bounds.2.trans_le (by
      nlinarith [mul_nonneg (by linarith [εsmall] : 0 ≤ 1 / 2 - 5 * ε / 4)
        cutoff_positive.le])
    have cell_margin (cell : {S : MonotoneStrip // S ∈ P.cells}) :
        ∀ z ∈ cell.val.carrier, 0 ≤ z.re + z.im →
          μ i * (z.re + z.im) ≤ z.re ∧ μ i * (z.re + z.im) ≤ z.im := by
      intro z member forward
      exact margin i z ((P.cover z).mpr ⟨cell.val, cell.property, member⟩) forward
    have fine_leaves (leaf : M.GeometricSectorLeaf F covered positive small i) :
        ∃ w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
          Q.projectedVertex w = F.geometricPosition leaf.val := by
      obtain ⟨w, position, _⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
      exact ⟨w, position⟩
    have leaf_coherent (leaf : M.GeometricSectorLeaf F covered positive small i) :
        D.ProjectedCoherentAt Q (F.geometricPosition leaf.val) := by
      obtain ⟨_, _, coherent⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
      exact coherent (R.completedDevelopment D)
    exact SectorForest.waterfall_circle_images_pairwise_disjoint R network.property D B fine_leaves
      (L.cap_footprint) deep P traces curvature budget
      εpositive.le (εsmall.trans_lt (by norm_num)) (fun f z => operator_bound _ f z)
      (fun cell => vertex_pinches cell.val cell.property) provenance represented leaf_coherent
      (numerical i) cell_margin radius_bounds.1 far outside
      (fun cell => terminal_tails cell.val cell.property)
      (fun cell empty nonempty => M.completionOutward_empty_circle_continuation positive small T
            height cutoff deep ⟨εpositive, εsmall⟩ D B
        face_geometry budget i cell.val (traces cell) (vertex_pinches cell.val cell.property)
        radius radius_bounds (outside_empty cell) empty nonempty) outside_empty

end Unfoldings.ConvexRoof
