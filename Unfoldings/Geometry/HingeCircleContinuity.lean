module

public import Unfoldings.Geometry.HingeGapRadius
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-! Original-source circle contacts move continuously through an actual outward hinge opening. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)

include nonzero radial in
/-- Closed bank membership and compact circles give continuity without differentiating the curve. -/
theorem continuous_hingeCirclePoint (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex hinge) < (r : ℝ)) :
    Continuous (R.hingeCirclePoint hinge nonzero angle radial r) := by
  let sphere := Metric.sphere R.start (r : ℝ)
  let f : Set.Icc 0 angle → sphere := fun θ =>
    ⟨R.hingeCirclePoint hinge nonzero angle radial r θ, by
      change dist (R.hingeCirclePoint hinge nonzero angle radial r θ) R.start = (r : ℝ)
      rw [dist_comm]
      exact R.hingeCirclePoint_radius hinge nonzero angle radial r θ⟩
  let back : Set.Icc 0 angle × sphere → ℂ := fun pair =>
    R.chain.vertex hinge + complexRotation (-pair.1.val) (pair.2.val - R.chain.vertex hinge)
  have continuous_back : Continuous back := by
    dsimp only [back, complexRotation_apply, polarRay]
    fun_prop
  have graph : f.graph = back ⁻¹' (R.suffix hinge).carrier := by
    ext pair
    rcases pair with ⟨θ, z⟩
    change f θ = z ↔ back (θ, z) ∈ (R.suffix hinge).carrier
    constructor
    · rintro rfl
      exact ((R.suffix hinge).mem_rotatedCarrier_iff_rotate_back θ.val _).mp
        (R.hingeCirclePoint_mem_suffix hinge nonzero angle radial r higher θ)
    · intro member
      have bank := ((R.suffix hinge).mem_rotatedCarrier_iff_rotate_back θ.val z.val).mpr member
      have whole : z.val ∈ (R.rotateSuffix hinge θ.val).carrier := by
        rw [(R.rotateSuffix hinge θ.val).carrier_split hinge]
        apply Or.inr
        rwa [R.rotateSuffix_suffix_carrier]
      have actual := (R.rotateSuffix hinge θ.val).radialPoint_mem (radial θ.val θ.property)
        (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r
      apply Subtype.ext
      apply (R.rotateSuffix hinge θ.val).eq_of_radius_eq (radial θ.val θ.property)
        (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) actual whole
      rw [R.rotateSuffix_start]
      change dist R.start (R.hingeCirclePoint hinge nonzero angle radial r θ) = dist R.start z.val
      rw [R.hingeCirclePoint_radius]
      exact (show dist R.start z.val = (r : ℝ) by
        have hz : dist z.val R.start = (r : ℝ) := z.property
        exact (dist_comm _ _).trans hz).symm
  have closed := ((R.suffix hinge).isClosed_carrier nonzero).preimage continuous_back
  rw [← graph] at closed
  have continuous : Continuous f := continuous_of_isClosed_graph closed
  exact continuous_subtype_val.comp continuous

variable (outward : (R.suffix hinge).Outward) (positive : 0 < angle) (small : angle < Real.pi)

/-- Above the hinge, the actual source-circle slice is an embedded arc parameterized by
its real opening angle. Both directions are continuous in the ambient subspace topology. -/
def hingeCircleSliceHomeomorph (positive : 0 < angle) (small : angle < Real.pi) (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex hinge) < (r : ℝ)) :
    Set.Icc 0 angle ≃ₜ
      {z : ℂ // z ∈ (R.suffix hinge).rotationGap outward nonzero angle ∧
        dist R.start z = (r : ℝ)} := by
  let f : Set.Icc 0 angle →
      {z : ℂ // z ∈ (R.suffix hinge).rotationGap outward nonzero angle ∧
        dist R.start z = (r : ℝ)} := fun θ =>
    ⟨R.hingeCirclePoint hinge nonzero angle radial r θ, by
      exact (Set.ext_iff.mp
        (R.range_hingeCirclePoint hinge outward nonzero angle positive small radial r higher)
        _).mp ⟨θ, rfl⟩⟩
  have injective : Function.Injective f := by
    intro θ ψ equal
    exact R.hingeCirclePoint_injective hinge outward nonzero angle positive small radial r higher
      (congrArg Subtype.val equal)
  have surjective : Function.Surjective f := by
    intro z
    have member : z.val ∈ (R.suffix hinge).rotationGap outward nonzero angle ∩
        {z | dist R.start z = (r : ℝ)} := z.property
    rw [← R.range_hingeCirclePoint hinge outward nonzero angle positive small radial r higher]
      at member
    obtain ⟨θ, equal⟩ := member
    exact ⟨θ, Subtype.ext equal⟩
  let e := Equiv.ofBijective f ⟨injective, surjective⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    ((R.continuous_hingeCirclePoint hinge nonzero angle radial r higher).subtype_mk _)

@[simp] theorem hingeCircleSliceHomeomorph_apply (r : ℝ≥0)
    (higher : dist R.start (R.chain.vertex hinge) < (r : ℝ)) (θ : Set.Icc 0 angle) :
    (R.hingeCircleSliceHomeomorph hinge nonzero angle radial outward
      positive small r higher θ).val =
      R.hingeCirclePoint hinge nonzero angle radial r θ := rfl

end Unfoldings.PolygonalRay
