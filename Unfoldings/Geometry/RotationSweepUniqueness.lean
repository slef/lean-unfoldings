module

public import Unfoldings.Geometry.RotationGapSweep
public import Unfoldings.Geometry.SourceRotation

/-! An actual nonapex point of a positive bank-rotation gap lies on a unique intermediate bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- Undo the actual source-fixed rotation to test membership in its whole bank. -/
theorem mem_rotatedCarrier_iff_rotate_back (θ : ℝ) (z : ℂ) :
    z ∈ R.rotatedCarrier θ ↔
      R.start + complexRotation (-θ) (z - R.start) ∈ R.carrier := by
  constructor
  · rintro ⟨x, member, equal⟩
    change R.start + complexRotation θ (x - R.start) = z at equal
    rw [← equal, add_sub_cancel_left, complexRotation_neg_cancel]
    simpa only [add_sub_cancel] using member
  · intro member
    refine ⟨R.start + complexRotation (-θ) (z - R.start), member, ?_⟩
    change R.start + complexRotation θ
      (R.start + complexRotation (-θ) (z - R.start) - R.start) = z
    rw [add_sub_cancel_left]
    have cancel := complexRotation_neg_cancel (-θ) (z - R.start)
    rw [neg_neg] at cancel
    rw [cancel]
    abel

include outward nonzero in
/-- Any nonapex contact between two genuinely rotated banks forces equal complex rotations. -/
theorem rotatedCarrier_contact_phase {θ ψ : ℝ} {z : ℂ}
    (first : z ∈ R.rotatedCarrier θ) (last : z ∈ R.rotatedCarrier ψ) (nonapex : z ≠ R.start) :
    polarRay θ = polarRay ψ := by
  obtain ⟨x, hx, at_x⟩ := first
  obtain ⟨y, hy, at_y⟩ := last
  change R.start + complexRotation θ (x - R.start) = z at at_x
  change R.start + complexRotation ψ (y - R.start) = z at at_y
  have radius (angle : ℝ) (p : ℂ)
      (equal : R.start + complexRotation angle (p - R.start) = z) :
      dist R.start p = dist R.start z := by
    rw [← equal, dist_eq_norm', dist_eq_norm']
    simp only [add_sub_cancel_left, (complexRotation angle).norm_map]
  have same := R.eq_of_radius_eq outward nonzero hx hy
    ((radius θ x at_x).trans (radius ψ y at_y).symm)
  subst y
  have not_source : x ≠ R.start := by
    intro equal
    rw [equal, sub_self, map_zero, add_zero] at at_x
    exact nonapex at_x.symm
  have rotated : complexRotation θ (x - R.start) = complexRotation ψ (x - R.start) :=
    add_left_cancel (at_x.trans at_y.symm)
  exact mul_right_cancel₀ (sub_ne_zero.mpr not_source) rotated

include outward nonzero in
/-- On any angle interval shorter than a full turn, nonapex contacts force the same real angle. -/
theorem rotatedCarrier_contact_angle {angle θ ψ : ℝ} (short : angle < 2 * Real.pi)
    (first_angle : θ ∈ Set.Icc 0 angle) (last_angle : ψ ∈ Set.Icc 0 angle) {z : ℂ}
    (first : z ∈ R.rotatedCarrier θ) (last : z ∈ R.rotatedCarrier ψ) (nonapex : z ≠ R.start) :
    θ = ψ := by
  have equal := R.rotatedCarrier_contact_phase outward nonzero first last nonapex
  exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    ⟨first_angle.1, first_angle.2.trans_lt short⟩
    ⟨last_angle.1, last_angle.2.trans_lt short⟩ (Subtype.ext equal)

include outward nonzero in
/-- Positive gap sweeps have no repeated intermediate bank away from their actual source. -/
theorem mem_rotationGap_iff_unique_sweep (angle : ℝ) (positive : 0 < angle)
    (small : angle < Real.pi) (z : ℂ) (nonapex : z ≠ R.start) :
    z ∈ R.rotationGap outward nonzero angle ↔
      ∃! θ : ℝ, θ ∈ Set.Icc 0 angle ∧ z ∈ R.rotatedCarrier θ := by
  constructor
  · intro member
    obtain ⟨θ, bounds, member⟩ :=
      (R.mem_rotationGap_iff_sweep outward nonzero angle positive small z).mp member
    refine ⟨θ, ⟨bounds, member⟩, fun ψ other => ?_⟩
    exact R.rotatedCarrier_contact_angle outward nonzero
      (small.trans (by linarith [Real.pi_pos])) other.1 bounds other.2 member nonapex
  · rintro ⟨θ, ⟨bounds, member⟩, _unique⟩
    exact (R.mem_rotationGap_iff_sweep outward nonzero angle positive small z).mpr
      ⟨θ, bounds, member⟩

end Unfoldings.PolygonalRay
