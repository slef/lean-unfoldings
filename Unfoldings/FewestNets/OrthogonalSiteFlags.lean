module

public import Unfoldings.FewestNets.SingleCellExpectation

/-! A site has its normalized area marginal in each orientation class. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open MeasureTheory

/-- An orthogonal placement is an actual ambient linear isometry. -/
def orthogonalIsometry (g : SpatialRotation) (reversed : Bool) : Space ≃ₗᵢ[ℝ] Space :=
  (isometry g).trans (if reversed then LinearIsometryEquiv.neg ℝ
    else LinearIsometryEquiv.refl ℝ Space)

@[simp] theorem orthogonalIsometry_apply (g : SpatialRotation) (reversed : Bool) (x : Space) :
    orthogonalIsometry g reversed x = orthogonalPlacement g reversed x := by
  cases reversed <;> rfl

theorem continuous_orthogonalPlacement (reversed : Bool) (x : Space) :
    Continuous (fun g : SpatialRotation => orthogonalPlacement g reversed x) := by
  have action := continuous_apply.comp (continuous_id.prodMk (continuous_const (y := x)))
  cases reversed
  · exact action
  · exact action.neg

/-- In either coset the direction of a unit vector is uniform on the sphere. -/
theorem map_orthogonalPlacement_probability (reversed : Bool) {x : Space} (unit : ‖x‖ = 1) :
    probability.map (fun g => orthogonalPlacement g reversed x) = uniformSphere := by
  cases reversed
  · exact map_linear_probability unit
  · have equal : (fun g => orthogonalPlacement g true x) = fun g => linear g (-x) := by
      funext g
      change -(linear g x) = _
      exact (map_neg (linear g) x).symm
    rw [equal]
    exact map_linear_probability (by simpa only [norm_neg] using unit)

/-- Continuity makes each geometric membership flag measurable. -/
def siteFlag (region : Set Space) (reversed : Bool) (x : Space) (g : SpatialRotation) : Bool :=
  @decide (orthogonalPlacement g reversed x ∈ region) (Classical.propDecidable _)

@[simp] theorem siteFlag_eq_true_iff (region : Set Space) (reversed : Bool)
    (x : Space) (g : SpatialRotation) :
    siteFlag region reversed x g = true ↔ orthogonalPlacement g reversed x ∈ region := by
  classical
  simp only [siteFlag, decide_eq_true_eq]

theorem measurableSet_siteFlag {region : Set Space} (measurable : MeasurableSet region)
    (reversed : Bool) (x : Space) : MeasurableSet {g | siteFlag region reversed x g = true} := by
  have eq : {g | siteFlag region reversed x g = true} =
      (fun g => orthogonalPlacement g reversed x) ⁻¹' region := by ext g; simp
  rw [eq]
  exact (continuous_orthogonalPlacement reversed x).measurable measurable

theorem integral_siteFlag {region : Set Space} (measurable : MeasurableSet region)
    (reversed : Bool) {x : Space} (unit : ‖x‖ = 1) :
    (∫ g, FewestNets.SingleCellCharge.membershipValue (siteFlag region reversed x g)
      ∂probability) = uniformSphere.real region := by
  let f := fun g => orthogonalPlacement g reversed x
  have indicator :
      (fun g => FewestNets.SingleCellCharge.membershipValue (siteFlag region reversed x g)) =
        (f ⁻¹' region).indicator (fun _ => (1 : ℝ)) := by
    funext g
    by_cases inside : f g ∈ region
    · have selected : siteFlag region reversed x g = true := (siteFlag_eq_true_iff _ _ _ _).mpr inside
      simp [FewestNets.SingleCellCharge.membershipValue, selected, inside]
    · have excluded : siteFlag region reversed x g = false :=
        Bool.eq_false_iff.mpr (fun selected => inside ((siteFlag_eq_true_iff _ _ _ _).mp selected))
      simp [FewestNets.SingleCellCharge.membershipValue, excluded, inside]
  have eval : Measurable f := (continuous_orthogonalPlacement reversed x).measurable
  rw [indicator]
  change (∫ g, (f ⁻¹' region).indicator 1 g ∂probability) = _
  rw [integral_indicator_one (eval measurable), Measure.real, ← Measure.map_apply eval measurable]
  change ((probability.map (fun g => orthogonalPlacement g reversed x)) region).toReal = _
  rw [map_orthogonalPlacement_probability reversed unit]
  rfl

end Unfoldings.SpatialRotation
