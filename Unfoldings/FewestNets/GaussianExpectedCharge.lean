module

public import Unfoldings.FewestNets.ExpectedNetworkCharge
public import Unfoldings.FewestNets.VoronoiOpenCrossings
public import Unfoldings.FewestNets.NormalComponentCharges
public import Unfoldings.Polyhedron.GaussianTwoSideBound

/-! The area-weighted expected charge of an actual Gaussian cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets SpatialRotation MeasureTheory InnerProductGeometry Real
open scoped BigOperators

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

open Classical in
theorem labelCutDegree_eq_filter_gaussianArcSeams {L : Type*} (lab : Space → L)
    (a : C.Vertex Set.univ) :
    labelCutDegree (lab ∘ N.normal) a =
      ((gaussianArcSeams N a).filter fun s => lab (N.normal (C.left s).face) ≠
        lab (N.normal (C.right s).face)).card := by
  unfold labelCutDegree gaussianArcSeams
  rw [Finset.filter_filter]
  congr 1
  ext s
  simp only [Finset.mem_filter, Function.comp_apply]
  constructor
  · rintro ⟨inc, diff⟩
    exact ⟨inc, fun eq => diff (congrArg lab eq), diff⟩
  · rintro ⟨inc, _, diff⟩
    exact ⟨inc, diff⟩

omit P in
theorem integrable_gaussian_voronoi_charge {I : Type*} [Finite I] [Nonempty I]
    (site : I → Space) (injective : Function.Injective site) (a : C.Vertex Set.univ) :
    Integrable (fun g => componentCharge
      (labelCutDegree (fun f => voronoiLabel site (N.normal f) g) a)) probability := by
  classical
  simp only [labelCutDegree]
  exact integrable_componentCharge_of_measurable probability _ _ (fun s _ =>
    measurableSet_voronoiLabel_ne site injective (N.normal (C.left s).face)
      (N.normal (C.right s).face))

include P in
/-- The expected contribution of an original vertex is bounded by its share
of the sphere's Gaussian area. The bound is independent of subdivisions. -/
theorem expected_gaussian_voronoi_charge_le_area
    {I J : Type*} [Finite I] [Nonempty I] [Fintype J]
    {site : I → Space} {endpoint : J → Bool → Space} {separation psi : ℝ}
    (H : VoronoiNetwork site endpoint separation psi)
    {eta : ℝ} (eta_pos : 0 < eta) (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i)
    (a : C.Vertex Set.univ) :
    let A := solidAngleMeasure.real (F.gaussianCell (F.gaussianSiteOfVertex a))
    (∫ g, componentCharge
      (labelCutDegree (fun f => voronoiLabel site (N.normal f) g) a) ∂probability) ≤
      (componentCoefficient (Fintype.card J) (networkLength endpoint) separation psi /
         sin (eta / 2)) * (A / (4 * π)) := by
  classical
  let ai := F.gaussianSiteOfVertex a
  let cell := F.gaussianCell ai
  let changed (g : SpatialRotation) (s : C.Seam) :=
    voronoiLabel site (N.normal (C.left s).face) g ≠
      voronoiLabel site (N.normal (C.right s).face) g
  let u (s : C.Seam) := N.normal (C.left s).face
  let v (s : C.Seam) := N.normal (C.right s).face
  let sides := gaussianArcSeams N a
  let t := sin (eta / 2)
  have charge (g : SpatialRotation) :
      labelCutDegree (fun f => voronoiLabel site (N.normal f) g) a =
        (sides.filter (changed g)).card :=
    labelCutDegree_eq_filter_gaussianArcSeams N (fun x => voronoiLabel site x g) a
  by_cases extreme : (ai : Space) ∈ F.vertexHull.extremePoints ℝ
  swap
  · have azero := F.solidAngle_gaussianCell_eq_zero_of_not_extreme ai extreme
    have each (g : SpatialRotation) : componentCharge
        (labelCutDegree (fun f => voronoiLabel site (N.normal f) g) a) = 0 :=
      P.normal_labelCutDegree_charge_eq_zero_of_nonextreme N
        (fun x => voronoiLabel site x g) a extreme
    have area_zero : solidAngleMeasure.real (F.gaussianCell (F.gaussianSiteOfVertex a)) = 0 := by
      change (solidAngleMeasure cell).toReal = 0
      rw [azero, ENNReal.toReal_zero]
    simp only [each, integral_zero, area_zero, zero_div, mul_zero, le_rfl]
  obtain ⟨d, deleted, d_nonneg, d_bound, _, few, big, small⟩ :=
    P.exists_omit_two_gaussian_sides N a extreme eta_pos min_angle
  let W := {i : F.hullSites // i ≠ ai}
  let f (w : W) := innerSL ℝ ((ai : Space) - (w.val : Space))
  have f_ne (w : W) : f w ≠ 0 := by
    intro eq
    have zero := DFunLike.congr_fun eq ((ai : Space) - (w.val : Space))
    change inner ℝ ((ai : Space) - (w.val : Space)) ((ai : Space) - (w.val : Space)) = 0 at zero
    exact w.property (Subtype.ext (sub_eq_zero.mp (inner_self_eq_zero.mp zero)).symm)
  have pos (x : Space) (hx : x ∈ cell) (w : W) : 0 ≤ f w x :=
    (F.mem_gaussianCone_iff_inner_sub.mp hx.1) w.val
  have diameter (x : Space) (xu : ‖x‖ = 1) (xp : ∀ w, 0 ≤ f w x)
      (y : Space) (yu : ‖y‖ = 1) (yp : ∀ w, 0 ≤ f w y) : angle x y ≤ d := by
    have from_inequalities (z : Space) (unit : ‖z‖ = 1) (ineq : ∀ w, 0 ≤ f w z) :
        z ∈ cell := by
      refine ⟨F.mem_gaussianCone_iff_inner_sub.mpr ?_, ?_⟩
      · intro w
        by_cases h : w = ai
        · subst w
          simp
        · exact ineq ⟨w, h⟩
      · simpa only [Metric.mem_sphere, dist_zero_right] using unit
    exact d_bound x (from_inequalities x xu xp) y (from_inequalities y yu yp)
  have linked (i : C.Seam) (hi : i ∈ sides) :
      ∃ b : C.Vertex Set.univ, C.seamGraph.IsLink i a b := by
    obtain ⟨inc, _⟩ := Finset.mem_filter.mp hi
    rcases (Finset.mem_filter.mp inc).2 with left | right
    · exact ⟨C.seamVertex i true, Or.inl ⟨left, rfl⟩⟩
    · exact ⟨C.seamVertex i false, Or.inr ⟨right, rfl⟩⟩
  have intersection (i : C.Seam) (b : C.Vertex Set.univ) (link : C.seamGraph.IsLink i a b) :
      cell ∩ F.gaussianCell (F.gaussianSiteOfVertex b) = closedMinorArc (u i) (v i) := by
    change F.gaussianCell (F.gaussianSiteOfVertex a) ∩
      F.gaussianCell (F.gaussianSiteOfVertex b) = _
    rcases link with ⟨l, r⟩ | ⟨l, r⟩ <;> rw [l, r]
    · exact P.gaussianCell_inter_seam_eq_normal_arc N i
    · rw [Set.inter_comm]
      exact P.gaussianCell_inter_seam_eq_normal_arc N i
  have arc_subset (i : C.Seam) (hi : i ∈ sides) : closedMinorArc (u i) (v i) ⊆ cell := by
    obtain ⟨b, link⟩ := linked i hi
    rw [← intersection i b link]
    exact Set.inter_subset_left
  obtain ⟨q, _, hemisphere⟩ := F.exists_gaussianCell_center P ai (F.gaussianCell_nonempty P ai)
  have non_antipodal (i : C.Seam) (hi : i ∈ sides) : u i + v i ≠ 0 := by
    intro zero
    have h := congrArg (fun z : Space => inner ℝ q z) zero
    rw [inner_add_right, inner_zero_right] at h
    exact (add_pos (hemisphere _ (arc_subset i hi (Set.mem_insert _ _)))
      (hemisphere _ (arc_subset i hi (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))).ne' h
  have boundary (i : C.Seam) (hi : i ∈ sides) (x : Space) (hx : x ∈ openMinorArc (u i) (v i)) :
      (∀ k, 0 ≤ f k x) ∧ ∃ k, f k x = 0 := by
    obtain ⟨b, link⟩ := linked i hi
    have both : x ∈ cell ∩ F.gaussianCell (F.gaussianSiteOfVertex b) := by
      rw [intersection i b link]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)
    have unequal : F.gaussianSiteOfVertex b ≠ ai := by
      change F.gaussianSiteOfVertex b ≠ F.gaussianSiteOfVertex a
      rcases link with ⟨l, r⟩ | ⟨l, r⟩ <;> rw [l, r]
      · exact fun h => gaussianSiteOfVertex_seam_ne (F := F) i (congrArg Subtype.val h.symm)
      · exact fun h => gaussianSiteOfVertex_seam_ne (F := F) i (congrArg Subtype.val h)
    refine ⟨pos x both.1, ⟨⟨F.gaussianSiteOfVertex b, unequal⟩, ?_⟩⟩
    have from_a := F.mem_gaussianCone_iff_inner_sub.mp both.1.1 (F.gaussianSiteOfVertex b)
    have from_b := F.mem_gaussianCone_iff_inner_sub.mp both.2.1 ai
    change inner ℝ ((ai : Space) - (F.gaussianSiteOfVertex b : Space)) x = 0
    simp only [inner_sub_left] at from_a from_b ⊢
    linarith only [from_a, from_b]
  have apart (i : C.Seam) (hi : i ∈ sides) (j : C.Seam) (hj : j ∈ sides) (ij : i ≠ j) :
      Disjoint (openMinorArc (u i) (v i)) (openMinorArc (u j) (v j)) := by
    obtain ⟨b, h⟩ := linked i hi
    obtain ⟨c, k⟩ := linked j hj
    exact P.disjoint_open_dual_seams_at_extreme_vertex N a b c extreme ij h k
      (Finset.mem_filter.mp hi).2
  have no_one : ∀ᵐ g ∂probability, (sides.filter (changed g)).card ≠ 1 :=
    Filter.Eventually.of_forall fun g => charge g ▸ P.labelCutDegree_ne_one _ a
  have integrable := integrable_componentCharge_of_measurable probability sides changed (fun i _ =>
    measurableSet_voronoiLabel_ne site H.siteInjective (u i) (v i))
  have labels := ae_voronoiLabel_mem_strict H.siteInjective N.normal N.unit
  have crossing := ae_open_network_crossing_of_voronoi_labels site H.siteInjective
    (fun j => endpoint j false) (fun j => endpoint j true) (fun j => H.edgeUnit j false)
    (fun j => H.edgeUnit j true) H.edgePositive
    (fun j => (H.edgeShort j).trans_lt (by linarith [pi_pos]))
    H.coversWalls (fun i : ↑sides => u i.val) (fun i => v i.val) (fun i => N.unit _)
    (fun i => N.unit _) (fun i => non_antipodal i.val i.property)
  have hits : ∀ᵐ g ∂probability, 3 ≤ (sides.filter (changed g)).card →
      ∀ i ∈ sides, changed g i → ∃ j x, x ∈ openMinorArc (u i) (v i) ∧
        x ∈ openMinorArc (linear g (endpoint j false)) (linear g (endpoint j true)) := by
    filter_upwards [labels, crossing] with g label cross
    intro _ i hi diff
    exact cross ⟨i, hi⟩ diff (label (C.left i).face) (label (C.right i).face)
  obtain ⟨⟨f₀, k₀⟩, _⟩ := C.vertexOfCorner_surjective Set.univ a
  have eta_small : eta < π := (min_angle f₀ k₀).trans_lt ((C.triangle f₀).cornerAngle_lt_pi k₀)
  have t_pos : 0 < t := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  let A := solidAngleMeasure.real cell
  let S := ∑ i : ↥(sides \ deleted), angle (u i.val) (v i.val)
  have residual : S = ∑ i ∈ sides \ deleted, angle (u i) (v i) := by
    unfold S
    refine Finset.sum_bij (fun i _ => i.val) (fun i _ => i.property)
      (fun i _ j _ eq => Subtype.ext eq) (fun i hi => ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  have big_sides : S * d ≤ 8 / t * A := by
    rw [div_mul_eq_mul_div, le_div_iff₀ t_pos, residual]
    exact big
  have small_sides (hd : d ≤ 1) : S * d ≤ 4 / (cos (d / 2) ^ 2 * t) * A := by
    have cos_pos : 0 < cos (d / 2) := cos_pos_of_mem_Ioo
      ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (pow_pos cos_pos _) t_pos)]
    calc
      _ = cos (d / 2) ^ 2 * (S * d * t) := by ring
      _ ≤ _ := by rw [residual]; exact small hd
  simp only [charge]
  exact expected_charge_of_voronoi_network H sides deleted few changed u v
    (fun _ _ => N.unit _) (fun _ _ => N.unit _) non_antipodal f f_ne boundary apart
    d_nonneg ENNReal.toReal_nonneg t_pos diameter small_sides big_sides integrable no_one hits

end Unfoldings.SpatialFolding.ConvexBoundary
