module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionSectorCircleGeometry
public import Unfoldings.Roof.AllSectorCircleSeparation
public import Unfoldings.Cap.WaterfallCircleNonoverlap
public import Unfoldings.Cap.WaterfallCircleExceptions
public import Unfoldings.Cap.WaterfallMapDistance

/-! A positive threshold chosen before both meshes separates actual roof-face interiors locally. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

theorem exists_uniform_completion_face_separation
    (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) (1 / 8), ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (3 : ℝ) / 4 ≤ Real.cos φ ∧
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {origin : Plane} (M : K.SectorForest t origin),
          ∀ {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
            (T : K.CompletionMesh φ region extra),
                ∀ cutoff : ℝ, 0 < cutoff → Metric.closedBall origin cutoff ⊆
                  interior (T.domain) →
                let inside := M.inside
                let _F := T.cornerTails inside
                let L := T.radialMesh M.inside
                let Q := L.cap
                letI := @Fintype.ofFinite _ L.mesh.toTriangulation.finite
                let R := (M.completionOutwardForest T positive small).val
                ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
                  Pairwise (fun f g => Disjoint
                    (D.projectedPlacement Q f '' (interior (Q.projectedTriangle f).carrier ∩
                      Metric.ball origin (ε * (cutoff / 16))))
                    (D.projectedPlacement Q g '' (interior (Q.projectedTriangle g).carrier ∩
                      Metric.ball origin (ε * (cutoff / 16))))) := by
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
    exists_uniform_completion_terminal_radial_waterfall.{u, v} t positive small εpositive
  refine ⟨ε, ⟨εpositive, εsmall⟩, φ, bounds, normal, ?_⟩
  intro Face _ C K tilt origin M region J extra T cutoff
    cutoff_positive deep
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
  change ∀ D : FacewiseDevelopment L.mesh.toTriangulation.pairedComplex R.retain,
    Pairwise (fun f g => Disjoint
      (D.projectedPlacement Q f '' (interior (Q.projectedTriangle f).carrier ∩
        Metric.ball origin (ε * (cutoff / 16))))
      (D.projectedPlacement Q g '' (interior (Q.projectedTriangle g).carrier ∩
        Metric.ball origin (ε * (cutoff / 16)))))
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
  choose P provenance represented coordinates terminal_tails vertex_pinches cells using strips
  let traces := fun i (cell : {S : MonotoneStrip // S ∈ (P i).cells}) =>
    Classical.choice (cells i cell.val cell.property)
  have leaf_vertices (i) (leaf : M.GeometricSectorLeaf F covered positive small i) :
      ∃ w : L.mesh.toTriangulation.pairedComplex.Vertex Set.univ,
        Q.projectedVertex w = F.geometricPosition leaf.val := by
    obtain ⟨w, position, _⟩ := leaves leaf.val leaf.property.1 leaf.property.2.1
    exact ⟨w, position⟩
  have leaf_coherent (i) (leaf : M.GeometricSectorLeaf F covered positive small i) :
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
  have separated : ∀ first last : Σ i : FiveSector, {S : MonotoneStrip // S ∈ (P i).cells},
      first ≠ last → ∀ radius ∈ Set.Ioo (0 : ℝ) (ε * (cutoff / 4)), radius ∉ exception →
      Disjoint ((traces first.1 first.2).outputFrame.symm ''
          ((traces first.1 first.2).value '' first.2.val.openSlab 0 cutoff ∩
            {z | ‖z - (traces first.1 first.2).center‖ = radius}))
        ((traces last.1 last.2).outputFrame.symm ''
          ((traces last.1 last.2).value '' last.2.val.openSlab 0 cutoff ∩
            {z | ‖z - (traces last.1 last.2).center‖ = radius})) := by
    intro first last different radius radius_bounds outside
    have outside_vertices := R.vertex_radius_not_mem_of_not_waterfallCircleExceptions positive small
      D calibration P traces outside
    have outside_empty := R.empty_radius_not_mem_of_not_waterfallCircleExceptions positive small
      D calibration P traces outside
    have continuations (i) (cell : {S : MonotoneStrip // S ∈ (P i).cells})
        (empty : (traces i cell).value '' cell.val.openSlab 0 cutoff ∩
          {z | ‖z - (traces i cell).center‖ = radius} = ∅)
        (nonempty : (cell.val.openSlab 0 cutoff).Nonempty) :
        Nonempty (B.EmptyCircleContinuation i (traces i cell) (cutoff / 4) radius) :=
      M.completionOutward_empty_circle_continuation positive small T
          height cutoff deep ⟨εpositive, εsmall⟩ D B face_geometry budget i cell.val
        (traces i cell) (vertex_pinches i cell.val cell.property) radius radius_bounds
        (outside_empty i cell) empty nonempty
    have room : 2 * radius < (1 / 2 - ε) * cutoff := by
      have coefficient : ε / 2 < 1 / 2 - ε := by linarith [εsmall]
      have product := mul_lt_mul_of_pos_right coefficient cutoff_positive
      nlinarith [radius_bounds.2]
    exact M.waterfall_circle_images_pairwise_disjoint_across_sectors F covered positive small
      R network.property D B leaf_vertices (L.cap_footprint)
      deep P traces curvature budget εpositive.le small_error operator_bound
      (fun i cell => vertex_pinches i cell.val cell.property) provenance represented leaf_coherent
      (fun i cell => terminal_tails i cell.val cell.property) continuations outside_empty
      (by linarith) first last different radius_bounds.1 room outside_vertices μ numerical
      cell_margins
      εpositive face_geometry
  let U := interior Q.footprint ∩
    Metric.ball origin (ε * (cutoff / 16))
  have U_open : IsOpen U := isOpen_interior.inter Metric.isOpen_ball
  have physical_room : 2 * (ε * (cutoff / 16)) < cutoff := by
    have coefficient : 2 * ε / 16 < 1 := by linarith [εsmall]
    have product := mul_lt_mul_of_pos_right coefficient cutoff_positive
    nlinarith
  have U_inside : U ⊆ sectorSweepInterior positive small origin cutoff :=
    fun _ member => closedBall_subset_sectorSweepInterior positive small _ physical_room
      (Metric.ball_subset_closedBall member.2)
  have image_bound : ∀ p ∈ U,
      ‖D.projectedMap Q p - D.projectedMap Q origin‖ < ε * (cutoff / 4) := by
    intro p member
    have bound := bank_control.projectedMap_distance_bounds R positive small D B εpositive.le
      (interior_subset member.1) (U_inside member)
    have near : ‖p - origin‖ < ε * (cutoff / 16) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using member.2
    have positive_ball : 0 < ε * (cutoff / 16) :=
      mul_pos εpositive (div_pos cutoff_positive (by norm_num))
    have coefficient : 1 + 2 * ε < 4 := by linarith [εsmall]
    have product := mul_lt_mul_of_pos_right coefficient positive_ball
    have compare : (1 + 2 * ε) * (ε * (cutoff / 16)) < ε * (cutoff / 4) := by
      nlinarith
    exact bound.2.trans_lt
      ((mul_lt_mul_of_pos_left near (by linarith [εpositive])).trans compare)
  have faces := R.face_interiors_disjoint_of_circle_separation positive small D calibration P traces
    U_open U_inside (ε * (cutoff / 4)) finite image_bound separated
  have restrict (f) :
      interior (Q.projectedTriangle f).carrier ∩ U =
        interior (Q.projectedTriangle f).carrier ∩
          Metric.ball origin (ε * (cutoff / 16)) := by
    have face_inside : (Q.projectedTriangle f).carrier ⊆ Q.footprint :=
      fun _ member => Q.footprint_eq_union_projectedTriangles.symm.subset
        (Set.mem_iUnion.mpr ⟨f, member⟩)
    ext p
    constructor
    · exact fun member => ⟨member.1, member.2.2⟩
    · exact fun member => ⟨member.1, interior_mono face_inside member.1, member.2⟩
  intro f g different
  have separation : Disjoint
      (D.projectedPlacement Q f '' (interior (Q.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement Q g '' (interior (Q.projectedTriangle g).carrier ∩ U)) :=
    faces different
  rw [restrict f, restrict g] at separation
  exact separation

end Unfoldings.ConvexRoof
