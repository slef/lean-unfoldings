module

public import Unfoldings.Geometry.SpatialRotationAction
public import Unfoldings.Geometry.SpatialRotationMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral

/-! Reflection pairing uses both cosets of the orthogonal group and fixes
each point of a selector side, including its possibly unequal endpoint cutoffs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open MeasureTheory

/-- Choose the orientation-preserving or reversing coset using central inversion. -/
def orthogonalPlacement (g : SpatialRotation) (reversed : Bool) (x : Space) : Space :=
  if reversed then -(linear g x) else linear g x

/-- A reflection of the template across a side's plane is right multiplication
by an actual rotation together with a change of orientation coset. -/
theorem exists_plane_reflection_placement {n : Space} (nonzero : n ≠ 0) :
    ∃ flip : SpatialRotation, ∀ (g : SpatialRotation) (reversed : Bool) (x : Space),
      orthogonalPlacement (g * flip) (!reversed) x =
        orthogonalPlacement g reversed ((ℝ ∙ n)ᗮ.reflection x) := by
  let reflection := (ℝ ∙ n)ᗮ.reflection
  let inv : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.neg ℝ
  let rotation := reflection.trans inv
  have old_det : LinearMap.det reflection.toLinearMap = -1 := by
    dsimp only [reflection]
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton nonzero, pow_one]
  have inv_map : inv.toLinearMap = (-1 : ℝ) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change -x = (-1 : ℝ) • x
    simp
  have inv_det : LinearMap.det inv.toLinearMap = -1 := by
    rw [inv_map, LinearMap.det_smul, LinearMap.det_id]
    norm_num [Space]
  have det_one : LinearMap.det rotation.toLinearMap = 1 := by
    change LinearMap.det (inv.toLinearMap.comp reflection.toLinearMap) = 1
    rw [LinearMap.det_comp, inv_det, old_det]
    norm_num
  let flip := ofIsometry rotation det_one
  have action (x : Space) : linear flip x = -(reflection x) := by
    change linear (ofIsometry rotation det_one) x = _
    rw [linear_ofIsometry]
    rfl
  refine ⟨flip, fun g reversed x => ?_⟩
  cases reversed <;> simp [orthogonalPlacement, action, LinearMap.comp_apply, reflection]

/-- The sum of the two coset integrals vanishes when reflection pairs their
signed contributions, without exchanging the side's endpoints. -/
theorem integral_cosets_cancel (first last : SpatialRotation → ℝ) (flip : SpatialRotation)
    (paired : ∀ᵐ g ∂probability, first g + last (g * flip) = 0) :
    (∫ g, first g ∂probability) + (∫ g, last g ∂probability) = 0 := by
  have opposite : (fun g => last (g * flip)) =ᵐ[probability] fun g => -first g := by
    filter_upwards [paired] with g equal
    linarith only [equal]
  have same : (∫ g, last (g * flip) ∂probability) = ∫ g, last g ∂probability :=
    (measurePreserving_mul_right probability flip).integral_comp
      (MeasurableEquiv.mulRight flip).measurableEmbedding last
  rw [integral_congr_ae opposite, integral_neg] at same
  linarith only [same]

/-- Delete the pairwise disjoint central regions after averaging over both
orientation cosets. Each side uses its own reflection. -/
theorem integral_cosets_eq_of_cancelling_regions {I : Type*} [Fintype I]
    (central : Bool → I → Set SpatialRotation)
    (measurable : ∀ b i, MeasurableSet (central b i))
    (disjoint : ∀ b, Pairwise fun i j => Disjoint (central b i) (central b j))
    (flip : I → SpatialRotation) (f : Bool → SpatialRotation → ℝ)
    (integrable : ∀ b, Integrable (f b) probability)
    (stable : ∀ i, ∀ᵐ g ∂probability,
      g ∈ central false i ↔ g * flip i ∈ central true i)
    (paired : ∀ i, ∀ᵐ g ∂probability, g ∈ central false i →
      f false g + f true (g * flip i) = 0) :
    (∫ g, f false g ∂probability) + (∫ g, f true g ∂probability) =
      (∫ g in (⋃ i, central false i)ᶜ, f false g ∂probability) +
        (∫ g in (⋃ i, central true i)ᶜ, f true g ∂probability) := by
  classical
  have cancel (i : I) : (∫ g in central false i, f false g ∂probability) +
      (∫ g in central true i, f true g ∂probability) = 0 := by
    rw [← integral_indicator (measurable false i), ← integral_indicator (measurable true i)]
    apply integral_cosets_cancel _ _ (flip i)
    filter_upwards [stable i, paired i] with g equiv opposite
    by_cases member : g ∈ central false i
    · simpa only [Set.indicator_of_mem member, Set.indicator_of_mem (equiv.mp member)] using
        opposite member
    · have other : g * flip i ∉ central true i := fun there => member (equiv.mpr there)
      simp [Set.indicator_of_notMem member, Set.indicator_of_notMem other]
  have vanish : (∫ g in ⋃ i, central false i, f false g ∂probability) +
      (∫ g in ⋃ i, central true i, f true g ∂probability) = 0 := by
    rw [integral_iUnion (measurable false) (disjoint false) (integrable false).integrableOn,
      integral_iUnion (measurable true) (disjoint true) (integrable true).integrableOn,
      tsum_fintype, tsum_fintype, ← Finset.sum_add_distrib]
    simp only [cancel, Finset.sum_const_zero]
  have decomposition (b : Bool) :=
    integral_add_compl (MeasurableSet.iUnion (measurable b)) (integrable b)
  linarith only [decomposition false, decomposition true, vanish]

end Unfoldings.SpatialRotation
