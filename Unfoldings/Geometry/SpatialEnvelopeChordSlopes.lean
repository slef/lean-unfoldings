module

public import Unfoldings.Geometry.SpatialEnvelope
public import Unfoldings.Geometry.SpatialPlaneSlopes
public import Unfoldings.Geometry.CompactCollinear
public import Unfoldings.Geometry.NonvertexChord
public import Unfoldings.Geometry.AffineSupportingChord

/-! An unchanged open chord forces all active supporting normal slopes to be collinear. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

def activeSlopes (p : Plane) : Set Plane :=
  {g | ∃ i, (family i).height p = height family p ∧ (family i).normalSlope = g}

/-- An unchanged rim chord also controls the slopes of added support planes. -/
theorem activeSlopes_collinear_of_unchanged_nonvertex
    (T : Triangle) (reference : Plane →ᵃ[ℝ] ℝ)
    (agrees : ∀ x ∈ T.carrier, height family x = reference x)
    {p : Plane} (member : p ∈ T.carrier) (regular : ¬ T.IsVertex p) :
    Collinear ℝ (activeSlopes family p) := by
  obtain ⟨a, ha, b, hb, different, between⟩ :=
    T.exists_open_chord_of_nonvertex member regular
  let d := b - a
  let height : Plane →ᵃ[ℝ] ℝ := (innerSL ℝ d).toLinearMap.toAffineMap +
    AffineMap.const ℝ Plane (reference b - reference a)
  have height_apply (z : Plane) : height z = inner ℝ d z +
      reference b - reference a := by
    change inner ℝ d z + (reference b - reference a) = _
    ring
  have proper : height ≠ 0 := by
    intro zero
    have at_zero := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A 0) zero
    have at_d := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A d) zero
    have first : height 0 = 0 := at_zero
    have last : height d = 0 := at_d
    rw [height_apply, inner_zero_right] at first
    rw [height_apply, real_inner_self_eq_norm_sq] at last
    have norm_zero : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
    exact (sub_ne_zero.mpr different.symm) (norm_eq_zero.mp norm_zero)
  apply collinear_of_affine_zero height proper
  rintro z ⟨g, active, rfl⟩
  let difference := (family g).height - reference
  have nonnegative (x : Plane) (hx : x ∈ T.carrier) : 0 ≤ difference x := by
    change 0 ≤ (family g).height x - reference x
    apply sub_nonneg.mpr
    exact (agrees x hx).symm.trans_le
      (AffineEnvelope.height_le (fun i => (family i).height) x g)
  have zero_at_p : difference p = 0 := by
    change (family g).height p - reference p = 0
    rw [active, agrees p member, sub_self]
  obtain ⟨first, last⟩ := affine_zero_endpoints_of_openSegment difference
    (nonnegative a ha) (nonnegative b hb) between zero_at_p
  change (family g).height a - reference a = 0 at first
  change (family g).height b - reference b = 0 at last
  have formula := (family g).height_difference a b
  rw [sub_eq_zero.mp first, sub_eq_zero.mp last] at formula
  rw [height_apply, real_inner_comm]
  change inner ℝ ((family g).normalSlope) (b - a) + reference b - reference a = 0
  linarith


end Unfoldings.SpatialEnvelope
