module

public import Unfoldings.Cap.UniformExtendedFaceSeparation
public import Unfoldings.Cap.ClosedFaceCircleContact

/-! Uniform identification of actual closed-face contacts away from finitely many image radii. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_extended_closed_contact
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, 0 < cutoff → Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest positive small T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ exception : Set ℝ, exception.Finite ∧
                    ∀ f g (p q : Plane),
                      p ∈ (Q.projectedTriangle f).carrier ∩
                        Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
                      q ∈ (Q.projectedTriangle g).carrier ∩
                        Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
                      0 < ‖D.projectedPlacement Q f p -
                        D.projectedMap Q (K.projectedVertex origin)‖ →
                      ‖D.projectedPlacement Q f p -
                        D.projectedMap Q (K.projectedVertex origin)‖ ∉ exception →
                      D.projectedPlacement Q f p = D.projectedPlacement Q g q → p = q := by
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
  obtain ⟨φ, bounds, normal, construct⟩ :=
    exists_uniform_extended_terminal_radial_waterfall.{u, v} t positive small εpositive
  refine ⟨ε, ⟨εpositive, εsmall⟩, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M internal source_height Z lower T conforming cutoff
    cutoff_positive deep
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
  change ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
    ∃ exception : Set ℝ, exception.Finite ∧
      ∀ f g (p q : Plane),
        p ∈ (Q.projectedTriangle f).carrier ∩
          Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
        q ∈ (Q.projectedTriangle g).carrier ∩
          Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
        0 < ‖D.projectedPlacement Q f p - D.projectedMap Q (K.projectedVertex origin)‖ →
        ‖D.projectedPlacement Q f p - D.projectedMap Q (K.projectedVertex origin)‖ ∉ exception →
        D.projectedPlacement Q f p = D.projectedPlacement Q g q → p = q
  intro D
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
  choose P provenance represented coordinates terminal_tails vertex_pinches cells using strips
  let traces := fun i (cell : {S : MonotoneStrip // S ∈ (P i).cells}) =>
    Classical.choice (cells i cell.val cell.property)
  have leaf_vertices (i) (leaf : M.GeometricSectorLeaf F covered positive small lower i) :
      ∃ w : L.partition.pairedComplex.Vertex Set.univ,
        Q.projectedVertex w = F.geometricPosition leaf.val := by
    obtain ⟨w, position, _⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
    exact ⟨w, position⟩
  have leaf_coherent (i) (leaf : M.GeometricSectorLeaf F covered positive small lower i) :
      D.ProjectedCoherentAt Q (F.geometricPosition leaf.val) := by
    obtain ⟨_, _, coherent⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
    exact coherent (R.completedDevelopment D)
  have cell_margins (i) (cell : {S : MonotoneStrip // S ∈ (P i).cells}) (z : ℂ)
      (member : z ∈ cell.val.carrier) (forward : 0 ≤ z.re + z.im) :
      μ i * (z.re + z.im) ≤ z.re ∧ μ i * (z.re + z.im) ≤ z.im :=
    margin i z (((P i).cover z).mpr ⟨cell.val, cell.property, member⟩) forward
  let exception := R.waterfallCircleExceptions positive small D calibration P traces
  have finite : exception.Finite := R.finite_waterfallCircleExceptions positive small D calibration
    P traces
  have small_error : ε < 1 / 2 := εsmall.trans_lt (by norm_num)
  have contacts : ∀ radius ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)), radius ∉ exception →
      ∀ f g (p q : Plane),
        p ∈ (Q.projectedTriangle f).carrier ∩
          Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
        q ∈ (Q.projectedTriangle g).carrier ∩
          Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) →
        ‖D.projectedPlacement Q f p - D.projectedMap Q (K.projectedVertex origin)‖ = radius →
        D.projectedPlacement Q f p = D.projectedPlacement Q g q → p = q := by
    intro radius radius_bounds outside
    have outside_vertices := R.vertex_radius_not_mem_of_not_waterfallCircleExceptions positive small
      D calibration P traces outside
    have outside_empty := R.empty_radius_not_mem_of_not_waterfallCircleExceptions positive small
      D calibration P traces outside
    have continuations (i) (cell : {S : MonotoneStrip // S ∈ (P i).cells})
        (empty : (traces i cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces i cell).center‖ = radius} = ∅)
        (nonempty : (cell.val.openSlab 0 cutoff).Nonempty) :
        Nonempty (B.EmptyCircleContinuation i (traces i cell) (cutoff / 4) radius) :=
      M.cornerExtendedOutward_empty_circle_continuation positive small T internal source_height
        lower conforming height cutoff deep ⟨εpositive, εsmall⟩ D B face_geometry budget i cell.val
        (traces i cell) (vertex_pinches i cell.val cell.property) radius radius_bounds
        (outside_empty i cell) empty nonempty
    have room : 2 * radius < (1 / 2 - ε) * cutoff := by
      have coefficient : ε / 2 < 1 / 2 - ε := by linarith [εsmall]
      have product := mul_lt_mul_of_pos_right coefficient cutoff_positive
      nlinarith [radius_bounds.2]
    have physical_room : 2 * (ε * (cutoff / 16)) < cutoff := by
      have coefficient : 2 * ε / 16 < 1 := by linarith [εsmall]
      have product := mul_lt_mul_of_pos_right coefficient cutoff_positive
      nlinarith
    have region : Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16)) ⊆
        sectorSweepInterior positive small (K.projectedVertex origin) cutoff :=
      fun _ member => closedBall_subset_sectorSweepInterior positive small _ physical_room
        (Metric.ball_subset_closedBall member)
    exact M.closed_face_circle_contact_same_projected_point F covered positive small lower R
      network.property D B leaf_vertices (L.partition.normalizedCap_footprint L.conforming lower)
      deep P traces curvature budget εpositive.le small_error operator_bound
      (fun i cell => vertex_pinches i cell.val cell.property) provenance represented leaf_coherent
      (fun i cell => terminal_tails i cell.val cell.property) continuations outside_empty
      (by linarith) radius_bounds.1 room outside_vertices μ numerical cell_margins
      εpositive face_geometry Metric.isOpen_ball region
  let U := Metric.ball (K.projectedVertex origin) (ε * (cutoff / 16))
  have physical_room : 2 * (ε * (cutoff / 16)) < cutoff := by
    have coefficient : 2 * ε / 16 < 1 := by linarith [εsmall]
    have product := mul_lt_mul_of_pos_right coefficient cutoff_positive
    nlinarith
  have U_inside : U ⊆ sectorSweepInterior positive small (K.projectedVertex origin) cutoff :=
    fun _ member => closedBall_subset_sectorSweepInterior positive small _ physical_room
      (Metric.ball_subset_closedBall member)
  have image_bound : ∀ f p, p ∈ (Q.projectedTriangle f).carrier → p ∈ U →
      ‖D.projectedPlacement Q f p - D.projectedMap Q (K.projectedVertex origin)‖ <
        ε * (cutoff / 4) := by
    intro f p face member
    have bound := bank_control.all_face_distance_bounds R positive small D B εpositive.le
      f face (U_inside member)
    have near : ‖p - K.projectedVertex origin‖ < ε * (cutoff / 16) := by
      simpa only [U, Metric.mem_ball, dist_eq_norm] using member
    have positive_ball : 0 < ε * (cutoff / 16) :=
      mul_pos εpositive (div_pos cutoff_positive (by norm_num))
    have coefficient : 1 + 2 * ε < 4 := by linarith [εsmall]
    have product := mul_lt_mul_of_pos_right coefficient positive_ball
    have compare : (1 + 2 * ε) * (ε * (cutoff / 16)) < ε * (cutoff / 4) := by
      nlinarith
    exact bound.2.trans_lt
      ((mul_lt_mul_of_pos_left near (by linarith [εpositive])).trans compare)
  refine ⟨exception, finite, ?_⟩
  intro f g p q first last positive_radius outside same
  exact contacts _ ⟨positive_radius, image_bound f p first.1 first.2⟩ outside
    f g p q first last rfl same

end Unfoldings.ConvexCap
