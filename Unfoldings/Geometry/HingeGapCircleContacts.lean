module

public import Unfoldings.Geometry.HingeCommonHeading
public import Unfoldings.Geometry.OpeningZero

/-! Every actual gap-circle point is a sweep contact, with strict angles at interior points. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (hinge : Fin (n + 1)) (nonzero : R.direction ≠ 0)
  (angle : ℝ) (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
  (outward : (R.suffix hinge).Outward) (positive : 0 < angle) (small : angle < Real.pi)

include outward positive small radial in
/-- Circle coverage includes the common hinge; no strict lower-radius premise is needed. -/
theorem hingeGap_circle_contact (r : ℝ≥0) {z : ℂ}
    (member : z ∈ (R.suffix hinge).rotationGap outward nonzero angle)
    (radius : dist R.start z = (r : ℝ)) :
    ∃ θ : Set.Icc 0 angle, R.hingeCirclePoint hinge nonzero angle radial r θ = z := by
  obtain ⟨θ, bounds, bank⟩ :=
    ((R.suffix hinge).mem_rotationGap_iff_sweep outward nonzero angle positive small z).mp member
  have whole : z ∈ (R.rotateSuffix hinge θ).carrier := by
    rw [(R.rotateSuffix hinge θ).carrier_split hinge]
    apply Or.inr
    rwa [R.rotateSuffix_suffix_carrier]
  refine ⟨⟨θ, bounds⟩, ?_⟩
  apply (R.rotateSuffix hinge θ).eq_of_radius_eq (radial θ bounds)
    (R.rotateSuffix_direction_ne_zero hinge θ nonzero)
    ((R.rotateSuffix hinge θ).radialPoint_mem (radial θ bounds)
      (R.rotateSuffix_direction_ne_zero hinge θ nonzero) r) whole
  rw [R.rotateSuffix_start]
  change dist R.start (R.hingeCirclePoint hinge nonzero angle radial r ⟨θ, bounds⟩) =
    dist R.start z
  exact (R.hingeCirclePoint_radius hinge nonzero angle radial r ⟨θ, bounds⟩).trans radius.symm

include outward positive small radial in
/-- Interior points lie strictly beyond the original-source hinge circle. -/
theorem hingeGap_interior_radius_gt_hinge {z : ℂ}
    (member : z ∈ interior ((R.suffix hinge).rotationGap outward nonzero angle)) :
    dist R.start (R.chain.vertex hinge) < dist R.start z := by
  by_contra below
  have contact := (Set.ext_iff.mp
    (R.hingeGap_inter_closedBall hinge outward nonzero angle positive small radial) z).mp
    ⟨interior_subset member, by
      apply Metric.mem_closedBall.mpr
      rw [dist_comm]
      exact le_of_not_gt below⟩
  have at_hinge : z = (R.suffix hinge).start := Set.mem_singleton_iff.mp contact
  have boundary : z ∈ frontier ((R.suffix hinge).rotationGap outward nonzero angle) := by
    rw [(R.suffix hinge).frontier_rotationGap outward nonzero angle
      (Real.sin_pos_of_pos_of_lt_pi positive small).ne']
    exact Or.inl (at_hinge ▸ (R.suffix hinge).start_mem)
  exact disjoint_interior_frontier.notMem_of_mem_left member boundary

include outward positive small radial in
/-- Interior gap points correspond to strict intermediate angles of the actual opening. -/
theorem hingeGap_interior_circle_contact (r : ℝ≥0) {z : ℂ}
    (member : z ∈ interior ((R.suffix hinge).rotationGap outward nonzero angle))
    (radius : dist R.start z = (r : ℝ)) :
    ∃ θ : Set.Icc 0 angle, 0 < θ.val ∧ θ.val < angle ∧
      R.hingeCirclePoint hinge nonzero angle radial r θ = z := by
  obtain ⟨θ, equal⟩ := R.hingeGap_circle_contact hinge nonzero angle radial outward positive small r
    (interior_subset member) radius
  have above : dist R.start (R.chain.vertex hinge) < (r : ℝ) :=
    radius ▸ R.hingeGap_interior_radius_gt_hinge hinge nonzero angle radial
      outward positive small member
  have bank := R.hingeCirclePoint_mem_suffix hinge nonzero angle radial r above θ
  rw [equal] at bank
  have sine : Real.sin angle ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi positive small).ne'
  have boundary : z ∉ frontier ((R.suffix hinge).rotationGap outward nonzero angle) :=
    fun on_boundary => disjoint_interior_frontier.notMem_of_mem_left member on_boundary
  have not_first : θ.val ≠ 0 := by
    intro zero
    have original := ((R.suffix hinge).mem_rotatedCarrier_iff_rotate_back θ.val z).mp bank
    rw [zero, neg_zero, complexRotation_apply, polarRay_zero, one_mul, add_sub_cancel] at original
    apply boundary
    rw [(R.suffix hinge).frontier_rotationGap outward nonzero angle sine]
    exact Or.inl original
  have not_last : θ.val ≠ angle := by
    intro last
    apply boundary
    rw [(R.suffix hinge).frontier_rotationGap outward nonzero angle sine]
    exact Or.inr (last ▸ bank)
  exact ⟨θ, lt_of_le_of_ne θ.property.1 not_first.symm,
    lt_of_le_of_ne θ.property.2 not_last, equal⟩

end Unfoldings.PolygonalRay
