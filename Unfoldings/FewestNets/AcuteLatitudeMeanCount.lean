module

public import Unfoldings.FewestNets.AcuteLatitudeBoundaryMetrics
public import Unfoldings.FewestNets.AcuteLatitudeCountScalars
public import Unfoldings.FewestNets.AcuteLatitudeBudget
public import Unfoldings.FewestNets.GaussianMeanCount

/-! Uniform orthogonal placement gives the revised acute component-count budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real MeasureTheory Cap SpatialRotation SingleCellCharge InnerProductGeometry

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

include positive small in
/-- Both the annular and polar selector families are closed and spherically convex. -/
theorem selectorSphere_closed_convex (key : Selector a) :
    IsClosed (selectorSphere positive small key) ∧ SphericalConvex (selectorSphere positive small key) := by
  rcases key with pole | i
  · exact ⟨(polarSelectorBoundary positive small pole).isClosed,
      (polarSelectorBoundary positive small pole).sphericalConvex⟩
  · exact ⟨(annularSelectorBoundary positive small i).isClosed,
      (annularSelectorBoundary positive small i).sphericalConvex⟩

include positive small in
/-- Either coset gives a generic placement of every original face normal. -/
theorem ae_orthogonal_avoids_selector_edges {I : Type*} [Finite I] (directions : I → Space)
    (unit : ∀ i, ‖directions i‖ = 1) (b : Bool) :
    ∀ᵐ g ∂probability, ∀ i (c : ChordFace a) j, (chordBasis positive small c).coord j
      (orthogonalIsometry g b (directions i)) ≠ 0 := by
  filter_upwards [ae_avoids_selector_edge_planes positive small directions unit] with g regular i c j
  cases b
  · exact regular i c j
  · change (chordBasis positive small c).coord j (-(linear g (directions i))) ≠ 0
    rw [map_neg, neg_ne_zero]
    exact regular i c j

include positive small in
/-- The marginal probabilities of the actual selectors sum to one. -/
theorem sum_uniformSphere_real_selectorSphere :
    (∑ key : Selector a, uniformSphere.real (selectorSphere positive small key)) = 1 := by
  classical
  let q := northLift 0
  let region (key : Selector a) := selectorSphere positive small key
  let flag (key : Selector a) (g : SpatialRotation) := siteFlag (region key) false q g
  have measured (key : Selector a) : MeasurableSet (region key) :=
    (selectorSphere_closed_convex positive small key).1.measurableSet
  have integrable (key : Selector a) :
      Integrable (fun g => membershipValue (flag key g)) probability :=
    integrable_membershipValue _ (measurableSet_siteFlag (measured key) false q)
  calc
    _ = ∑ key, ∫ g, membershipValue (flag key g) ∂probability :=
      Finset.sum_congr rfl (fun key _ => (integral_siteFlag (measured key) false northLift_zero_unit).symm)
    _ = ∫ g, ∑ key, membershipValue (flag key g) ∂probability :=
      (integral_finsetSum _ fun key _ => integrable key).symm
    _ = ∫ _ : SpatialRotation, (1 : ℝ) ∂probability := by
      apply integral_congr_ae
      filter_upwards [ae_avoids_selector_edge_planes positive small (fun _ : Unit => q)
        (fun _ => northLift_zero_unit)] with g generic
      let x := linear g q
      have unit : ‖x‖ = 1 := ((isometry g).norm_map q).trans northLift_zero_unit
      obtain ⟨key, here⟩ := exists_selectorSphere positive small x unit
      have selected : flag key g = true := (siteFlag_eq_true_iff _ _ _ _).mpr here
      rw [Finset.sum_eq_single key]
      · simp only [selected, membershipValue, ite_true]
      · intro other _ different
        have outside : flag other g = false := Bool.eq_false_iff.mpr fun yes =>
          different (selectorSphere_unique positive small
            ((siteFlag_eq_true_iff _ _ _ _).mp yes) here (generic ()))
        simp only [outside, membershipValue, Bool.false_eq_true, ite_false]
      · simp
    _ = 1 := by rw [integral_const, probReal_univ, one_smul]

/-- The scalar excess of a selector depends only on whether it is polar or annular. -/
def selectorCountAllowance (key : Selector a) : ℝ :=
  key.elim (fun _ => 8.51 / a ^ 2) (fun _ => 3 / a ^ 2)

include positive small in
/-- These individual allowances sum to less than the revised global budget. -/
theorem selectorCountAllowance_sum_lt :
    2 + (∑ key : Selector a, selectorCountAllowance key) < 1440 / a ^ 4 := by
  have sum : (∑ key : Selector a, selectorCountAllowance key) =
      17.02 / a ^ 2 + (triangleCount a : ℝ) * (3 / a ^ 2) := by
    rw [Fintype.sum_sum_type]
    simp only [selectorCountAllowance, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, card_annularTriangle, nsmul_eq_mul]
    ring
  rw [sum]
  have count := mul_le_mul_of_nonneg_right (triangleCount_lt positive small).le
    (by positivity : 0 ≤ 3 / a ^ 2)
  linarith only [count, acute_latitude_component_bound positive small]

end Unfoldings.FewestNets.AcuteLatitudeGrid

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets AcuteLatitudeGrid SphericalSelectorBoundary SpatialRotation MeasureTheory
  InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

private theorem nonneg_crossingBudget {J : Type*} [Fintype J] {region : Set Space}
    {B : SphericalSelectorBoundary J region} (M : MetricData B) : 0 ≤ M.crossingBudget :=
  (div_nonneg (Finset.sum_nonneg (fun j _ => (M.endpointFactor_pos j.1 j.2).le)) pi_pos.le).trans
    (le_max_left _ _)

include P in
set_option maxHeartbeats 1500000 in
/-- The actual annular and polar selectors satisfy their respective expected
component-count bounds under the same uniform orthogonal placement. -/
theorem mean_acuteLatitudeSelectedCount_le
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ π / 2 - a) (key : Selector a) :
    let region := selectorSphere positive small key
    ((∫ g, gaussianSelectedCount N region false g ∂probability) +
      (∫ g, gaussianSelectedCount N region true g ∂probability)) / 2 ≤
      2 * uniformSphere.real region + selectorCountAllowance key := by
  have eta_pos : 0 < 2 * a := by positivity
  have eta_small : 2 * a ≤ π / 2 := by linarith only [small, pi_pos]
  have minimum (f : Face) (i : Fin 3) : 2 * a ≤ (C.triangle f).cornerAngle i :=
    input_cornerAngle_lower (C.triangle f) (angles f) i
  obtain ⟨q, unit, hemisphere⟩ := exists_selectorSphere_hemisphere positive small key
  rcases key with pole | i
  · obtain ⟨M, budget⟩ := exists_polarSelectorMetric_crossingBudget_le positive small pole
    have count := P.mean_gaussianSelectedCount_le N M q unit hemisphere eta_pos eta_small minimum
    have coefficient := local_count_prefactor positive small M.separation_pos.le M.separation_small
    have estimate := polar_count_excess_lt positive coefficient.le (nonneg_crossingBudget M)
      budget (polar_size_bounds positive small).2.1
    exact count.trans (add_le_add le_rfl estimate.le)
  · let M := annularSelectorMetric positive small i
    have count := P.mean_gaussianSelectedCount_le N M q unit hemisphere eta_pos eta_small minimum
    have coefficient := local_count_prefactor positive small M.separation_pos.le M.separation_small
    have estimate := triangle_count_excess_lt positive coefficient.le (nonneg_crossingBudget M)
      (annularSelectorMetric_crossingBudget_lt positive small i).le
    exact count.trans (add_le_add le_rfl estimate.le)

end Unfoldings.SpatialFolding.ConvexBoundary
