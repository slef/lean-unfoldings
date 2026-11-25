module

public import Unfoldings.Polyhedron.GaussianChartOrientation
public import Unfoldings.Geometry.FramedSphericalChordPerimeter
public import Unfoldings.Geometry.DirectionFrame
public import Unfoldings.Geometry.PlanarConjugation
public import Unfoldings.Geometry.SolidAngleSymmetry
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Both perimeter bounds for the genuine sides of an actual extreme Gaussian cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open Cap InnerProductGeometry MeasureTheory
open scoped BigOperators
attribute [local instance] Complex.finrank_real_complex_fact

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem areaForm_repr_symm (x y : Plane) :
    Complex.orientation.areaForm (Complex.orthonormalBasisOneI.repr.symm x)
      (Complex.orthonormalBasisOneI.repr.symm y) = orient 0 x y := by
  rw [Complex.areaForm]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (orient_complex_repr_zero (Complex.orthonormalBasisOneI.repr.symm x)
      (Complex.orthonormalBasisOneI.repr.symm y)).symm

private theorem chord_turn_eq_chordSide {n : ℕ} (p : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    Complex.orientation.areaForm (p (finRotate (n + 1) i) - p i)
        (p (finRotate (n + 1) (finRotate (n + 1) i)) - p (finRotate (n + 1) i)) =
      chordSide p i (p (finRotate (n + 1) (finRotate (n + 1) i))) := by
  let q := finRotate (n + 1)
  change _ = Complex.orientation.areaForm (p (q i) - p i) (p (q (q i)) - p i)
  rw [show p (q (q i)) - p i = (p (q (q i)) - p (q i)) + (p (q i) - p i) by abel,
    map_add, Complex.orientation.areaForm_apply_self, add_zero]

open Classical in
include P in
/-- A pair of omitted genuine sides works for both the global and the
diameter-sensitive area bounds. All sides and sites belong to the input mesh. -/
theorem exists_omit_two_gaussian_sides_of_small_minimum
    (a : C.Vertex Set.univ)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    {eta : ℝ} (eta_pos : 0 < eta) (eta_small : eta ≤ Real.pi / 2)
    (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    let cell := F.gaussianCell (F.gaussianSiteOfVertex a)
    ∃ (d : ℝ) (removed : Finset C.Seam), 0 ≤ d ∧
      (∀ u ∈ cell, ∀ v ∈ cell, angle u v ≤ d) ∧
      removed ⊆ gaussianArcSeams N a ∧ removed.card ≤ 2 ∧
      let S := ∑ s ∈ gaussianArcSeams N a \ removed,
        angle (N.normal (C.left s).face) (N.normal (C.right s).face)
      S * d * Real.sin eta ≤ 8 * solidAngleMeasure.real cell ∧
      (d ≤ 1 → Real.cos (d / 2) ^ 2 * (S * d * Real.sin eta) ≤
        4 * solidAngleMeasure.real cell) := by
  classical
  let ai := F.gaussianSiteOfVertex a
  let cell := F.gaussianCell ai
  obtain ⟨q, hq, strict, hemisphere⟩ := F.exists_strict_gaussianCell_center P ai extreme
  let K := F.gaussianChartRegion ai q
  let L := northFrame q
  obtain ⟨compact, convex, zero, chart_disk, chart⟩ :=
    F.gaussianChartRegion_properties ai hq hemisphere
  have disk (x : Plane) (hx : x ∈ K) : ‖x‖ ≤ 1 :=
    (by simpa only [Metric.mem_ball, dist_zero_right] using chart_disk hx : ‖x‖ < 1).le
  have spherical (x : Space) (hx : x ∈ cell) : ‖x‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hx.2
  have cont : ContinuousOn (fun w : Space × Space => angle w.1 w.2) (cell ×ˢ cell) := by
    intro w hw
    have u_ne : w.1 ≠ 0 := norm_ne_zero_iff.mp (by rw [spherical _ hw.1]; norm_num)
    have v_ne : w.2 ≠ 0 := norm_ne_zero_iff.mp (by rw [spherical _ hw.2]; norm_num)
    exact (continuousAt_angle u_ne v_ne).continuousWithinAt
  obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, max_d⟩ := ((F.isCompact_gaussianCell ai).prod
    (F.isCompact_gaussianCell ai)).exists_isMaxOn
      ⟨(q, q), hq, hq⟩ cont
  let d := angle u v
  have d_bound : ∀ x ∈ cell, ∀ y ∈ cell, angle x y ≤ d := fun x hx y hy =>
    isMaxOn_iff.mp max_d (x, y) ⟨hx, hy⟩
  have exists_chart (z : Space) (hz : z ∈ cell) : ∃ x ∈ K, inverseStereographic x = L z := by
    have member := Set.mem_image_of_mem L hz
    rw [← chart] at member
    exact member
  obtain ⟨x, hx, ux⟩ := exists_chart u hu
  obtain ⟨y, hy, vy⟩ := exists_chart v hv
  have base_length : d ≤ 2 * dist x y := by
    rw [dist_eq_norm]
    calc
      d = angle (inverseStereographic x) (inverseStereographic y) := by
        rw [ux, vy]
        exact (L.toLinearIsometry.angle_map u v).symm
      _ ≤ _ := angle_inverseStereographic_le (disk x hx) (disk y hy)
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link a
  have nonempty := P.nonempty_cyclicRunStarts_of_extreme N c covers extreme
  obtain ⟨m, count⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr nonempty)
  let Z := compressedLinkNormal N c count
  let p := stereographicCoord ∘ L ∘ Z
  let next := finRotate (m + 1)
  let s := P.runStartGaussianSeamEquiv N c closes covers count
  obtain ⟨pinj, in_frontier, _, _⟩ := P.compressedLinkNormal_chart_arcs N c closes covers count
    extreme q hq strict hemisphere
  have every_point (i : Fin (m + 1)) : p i ∈ K := by
    apply compact.isClosed.frontier_subset
    apply in_frontier i
    exact Set.mem_image_of_mem _ (Set.mem_insert _ _)
  have minimum (i : Fin (m + 1)) :
      eta ≤ angle (p (next i) - p i) (p (next (next i)) - p (next i)) := by
    have h := P.min_angle_le_of_gaussian_chart_chords N c closes covers count extreme q hq strict
      hemisphere eta_pos min_angle (next i)
    change eta ≤ angle (p (next i) - p (next.symm (next i)))
      (p (next (next i)) - p (next i)) at h
    rwa [next.symm_apply_apply] at h
  let G := directionFrame (y - x)
  let J := Complex.orthonormalBasisOneI.repr.symm
  let r := J ∘ G ∘ p
  let H := G.trans planeConjugation
  let r' := J ∘ H ∘ p
  have horizontal_G : G x 1 = G y 1 := by
    have h := directionFrame_vertical (y - x)
    change G (y - x) 1 = 0 at h
    rw [map_sub] at h
    change G y 1 - G x 1 = 0 at h
    linarith only [h]
  have horizontal_H : H x 1 = H y 1 := by
    change planeConjugation (G x) 1 = planeConjugation (G y) 1
    rw [planeConjugation_apply, planeConjugation_apply]
    change -(G x 1) = -(G y 1)
    rw [horizontal_G]
  have reflect (i j : Fin (m + 1)) : chordSide r' i (r' j) = -chordSide r i (r j) := by
    change Complex.orientation.areaForm
        (J (planeConjugation (G (p (next i)))) - J (planeConjugation (G (p i))))
        (J (planeConjugation (G (p j))) - J (planeConjugation (G (p i)))) =
      -Complex.orientation.areaForm (J (G (p (next i))) - J (G (p i)))
        (J (G (p j)) - J (G (p i)))
    simp only [← J.map_sub, ← planeConjugation.map_sub]
    have reflected (u v : Plane) :
        Complex.orientation.areaForm (J (planeConjugation u)) (J (planeConjugation v)) =
          -Complex.orientation.areaForm (J u) (J v) :=
      (areaForm_repr_symm _ _).trans ((orient_planeConjugation u v).trans
        (congrArg Neg.neg (areaForm_repr_symm u v).symm))
    exact reflected _ _
  have orientation := P.gaussian_chart_chord_orientation N c closes covers count extreme q hq
    strict hemisphere (G.trans J)
  have some_frame : ∃ T : Plane ≃ₗᵢ[ℝ] Plane, T x 1 = T y 1 ∧
      let r := J ∘ T ∘ p
      (∀ i j, 0 ≤ chordSide r i (r j)) ∧
        (∀ i, 0 < chordSide r i (r (next (next i)))) := by
    rcases orientation with ⟨nonneg, turns⟩ | ⟨nonpos, turns⟩
    · exact ⟨G, horizontal_G, nonneg, turns⟩
    · refine ⟨H, horizontal_H, fun i j => ?_, fun i => ?_⟩
      · change 0 ≤ chordSide r' i (r' j)
        rw [reflect]
        exact neg_nonneg.mpr (nonpos i j)
      · change 0 < chordSide r' i (r' (next (next i)))
        rw [reflect]
        exact neg_pos.mpr (turns i)
  obtain ⟨T, horizontal, support, turns⟩ := some_frame
  obtain ⟨deleted, few, planar⟩ := exists_omit_two_cyclic_spherical_chords_of_small_minimum compact convex disk
    hx hy (angle_nonneg u v) base_length T horizontal p every_point pinj eta_pos eta_small minimum
    support (fun i => by rw [chord_turn_eq_chordSide]; exact turns i)
  let edge := next.trans s
  let physical : Fin (m + 1) ↪ C.Seam :=
    ⟨fun i => (edge i).val, Subtype.val_injective.comp edge.injective⟩
  let removed := deleted.map physical
  have map_all : (Finset.univ : Finset (Fin (m + 1))).map physical = gaussianArcSeams N a := by
    ext t
    constructor
    · intro ht
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ht
      exact (edge i).property
    · intro ht
      obtain ⟨i, hi⟩ := edge.surjective ⟨t, ht⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩
  have omit_subset : removed ⊆ gaussianArcSeams N a := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ht
    exact (edge i).property
  have map_remain : (Finset.univ \ deleted).map physical = gaussianArcSeams N a \ removed := by
    rw [Finset.map_sdiff, map_all]
  have q_unit : ‖q‖ = 1 := spherical q hq
  have inverse (i : Fin (m + 1)) : inverseStereographic (p i) = L (Z i) := by
    have mem : Z i ∈ Set.range (linkNormals N c ∘ cyclicRunStart (linkNormals N c) count) :=
      ⟨i, rfl⟩
    rw [range_compressed_linkNormals N c covers count] at mem
    obtain ⟨f, j, at_a, normal⟩ := mem
    have on_cell : Z i ∈ cell := by
      rw [← normal]
      exact Eq.mp (congrArg (fun w => N.normal f ∈ F.gaussianCell (F.gaussianSiteOfVertex w)) at_a)
        (F.normal_mem_gaussianCell_of_corner N f j)
    have up : 0 < L (Z i) 2 := by
      change 0 < northFrame q (Z i) 2
      rw [northFrame_height q q_unit]
      exact hemisphere _ on_cell
    have height : -1 < L (Z i) 2 := by linarith only [up]
    exact inverseStereographic_stereographicCoord
      ((L.norm_map _).trans (spherical _ on_cell)) height
  have arc_length (i : Fin (m + 1)) :
      angle (N.normal (C.left (physical i)).face) (N.normal (C.right (physical i)).face) =
        angle (inverseStereographic (p i)) (inverseStereographic (p (next i))) := by
    rw [inverse i, inverse (next i)]
    have angle_map : angle (L (Z i)) (L (Z (next i))) = angle (Z i) (Z (next i)) :=
      L.toLinearIsometry.angle_map _ _
    rw [angle_map]
    have h := P.compressedLinkNormal_arcEnds N c closes covers count (next i)
    change HasGaussianArcEnds N (physical i) (Z (next.symm (next i))) (Z (next i)) at h
    rw [next.symm_apply_apply] at h
    rcases h with ⟨first, last⟩ | ⟨first, last⟩ <;> rw [first, last]
    exact angle_comm _ _
  let S := ∑ e ∈ gaussianArcSeams N a \ removed,
    angle (N.normal (C.left e).face) (N.normal (C.right e).face)
  have planar_bound : S * d * Real.sin eta ≤ 16 * (volume : Measure Plane).real K := by
    change (∑ e ∈ gaussianArcSeams N a \ removed,
      angle (N.normal (C.left e).face) (N.normal (C.right e).face)) *
        d * Real.sin eta ≤ _
    rw [← map_remain, Finset.sum_map]
    simp only [arc_length]
    exact planar
  have area : solidAngleMeasure.real (inverseStereographic '' K) = solidAngleMeasure.real cell := by
    change (solidAngleMeasure (inverseStereographic '' K)).toReal = (solidAngleMeasure cell).toReal
    rw [chart, solidAngleMeasure_image L (F.isCompact_gaussianCell ai).measurableSet
      Set.inter_subset_right]
  have star := convex.starConvex zero
  have few_removed : removed.card ≤ 2 := by simpa only [removed, Finset.card_map] using few
  refine ⟨d, removed, angle_nonneg u v, d_bound, omit_subset, few_removed, ?_, ?_⟩
  · have big := two_side_bound_of_planar_area compact star disk planar_bound
    rwa [area] at big
  · intro small
    have radius (z : Plane) (hz : z ∈ K) :
        angle (northLift 0) (inverseStereographic z) ≤ d := by
      have mem := Set.mem_image_of_mem inverseStereographic hz
      rw [chart] at mem
      obtain ⟨w, hw, eq⟩ := mem
      rw [← eq, ← northFrame_center q q_unit]
      exact (L.toLinearIsometry.angle_map q w).le.trans (d_bound q hq w hw)
    have sharper := two_side_bound_of_angular_radius compact star
      (show d < Real.pi / 2 by linarith [Real.pi_gt_three]) radius planar_bound
    rwa [area] at sharper

open Classical in
include P in
/-- The two-side perimeter bounds with the sine of the minimum turn capped at
a right angle. The same omitted sides satisfy both bounds. -/
theorem exists_omit_two_gaussian_sides_sharp
    (a : C.Vertex Set.univ)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    {eta : ℝ} (eta_pos : 0 < eta) (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    let cell := F.gaussianCell (F.gaussianSiteOfVertex a)
    ∃ (d : ℝ) (removed : Finset C.Seam), 0 ≤ d ∧
      (∀ u ∈ cell, ∀ v ∈ cell, angle u v ≤ d) ∧
      removed ⊆ gaussianArcSeams N a ∧ removed.card ≤ 2 ∧
      let S := ∑ s ∈ gaussianArcSeams N a \ removed,
        angle (N.normal (C.left s).face) (N.normal (C.right s).face)
      S * d * Real.sin (min eta (Real.pi / 2)) ≤ 8 * solidAngleMeasure.real cell ∧
      (d ≤ 1 → Real.cos (d / 2) ^ 2 * (S * d * Real.sin (min eta (Real.pi / 2))) ≤
        4 * solidAngleMeasure.real cell) :=
  P.exists_omit_two_gaussian_sides_of_small_minimum N a extreme
    (eta := min eta (Real.pi / 2))
    (lt_min eta_pos (by linarith only [Real.pi_pos])) (min_le_right _ _)
    (fun f i => (min_le_left _ _).trans (min_angle f i))

open Classical in
include P in
/-- The half-angle form of the two-side bound for a general minimum corner angle. -/
theorem exists_omit_two_gaussian_sides
    (a : C.Vertex Set.univ)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    {eta : ℝ} (eta_pos : 0 < eta) (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    let cell := F.gaussianCell (F.gaussianSiteOfVertex a)
    ∃ (d : ℝ) (removed : Finset C.Seam), 0 ≤ d ∧
      (∀ u ∈ cell, ∀ v ∈ cell, angle u v ≤ d) ∧
      removed ⊆ gaussianArcSeams N a ∧ removed.card ≤ 2 ∧
      let S := ∑ s ∈ gaussianArcSeams N a \ removed,
        angle (N.normal (C.left s).face) (N.normal (C.right s).face)
      S * d * Real.sin (eta / 2) ≤ 8 * solidAngleMeasure.real cell ∧
      (d ≤ 1 → Real.cos (d / 2) ^ 2 * (S * d * Real.sin (eta / 2)) ≤
        4 * solidAngleMeasure.real cell) :=
  P.exists_omit_two_gaussian_sides_of_small_minimum N a extreme (eta := eta / 2)
    (by linarith only [eta_pos])
    (by
      obtain ⟨n, c, _, _⟩ := P.exists_cyclic_link a
      have bound := (min_angle _ _).trans
        ((C.triangle c.first.val.1.1).cornerAngle_lt_pi c.first.val.1.2).le
      linarith only [bound])
    (fun f i => (by linarith only [eta_pos] : eta / 2 ≤ eta).trans (min_angle f i))

end Unfoldings.SpatialFolding.ConvexBoundary
