module

public import Unfoldings.Cap.NormalImage
public import Unfoldings.Cap.ClipSupportPolygons
public import Unfoldings.Geometry.CompactCollinear
public import Unfoldings.Geometry.NonvertexChord
public import Unfoldings.Geometry.AffineSupportingChord

/-! All active original support slopes are collinear at a regular original cap point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def activeSlopes (p : Plane) : Set Plane :=
  {g | ∃ f, K.supportHeight f p = K.roofHeight p ∧ K.normalSlope f = g}

theorem roofHeight_eq_supportHeight_of_mem_projectedTriangle (f : Face) {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier) : K.roofHeight p = K.supportHeight f p :=
  (K.mem_roofCell_iff f p).mp
    ((K.projectedTriangle_subset_clippedSupportCell (Z := 0) le_rfl f member).2)

/-- A nonvertex original face point gives a genuine supporting chord for every active plane. -/
theorem activeSlopes_collinear_of_nonvertex (f : Face) {p : Plane}
    (member : p ∈ (K.projectedTriangle f).carrier)
    (regular : ¬ (K.projectedTriangle f).IsVertex p) :
    Collinear ℝ (K.activeSlopes p) := by
  obtain ⟨a, ha, b, hb, different, between⟩ :=
    (K.projectedTriangle f).exists_open_chord_of_nonvertex member regular
  let d := b - a
  let height : Plane →ᵃ[ℝ] ℝ := (innerSL ℝ d).toLinearMap.toAffineMap +
    AffineMap.const ℝ Plane (K.supportHeight f b - K.supportHeight f a)
  have height_apply (z : Plane) : height z = inner ℝ d z +
      K.supportHeight f b - K.supportHeight f a := by
    change inner ℝ d z + (K.supportHeight f b - K.supportHeight f a) = _
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
  let difference := K.supportHeight g - K.supportHeight f
  have nonnegative (x : Plane) (hx : x ∈ (K.projectedTriangle f).carrier) : 0 ≤ difference x := by
    change 0 ≤ K.supportHeight g x - K.supportHeight f x
    apply sub_nonneg.mpr
    exact (K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f hx).symm.trans_le
      (K.roofHeight_le_supportHeight x g)
  have zero_at_p : difference p = 0 := by
    change K.supportHeight g p - K.supportHeight f p = 0
    rw [active, K.roofHeight_eq_supportHeight_of_mem_projectedTriangle f member, sub_self]
  obtain ⟨first, last⟩ := affine_zero_endpoints_of_openSegment difference
    (nonnegative a ha) (nonnegative b hb) between zero_at_p
  change K.supportHeight g a - K.supportHeight f a = 0 at first
  change K.supportHeight g b - K.supportHeight f b = 0 at last
  have formula := K.supportHeight_difference g a b
  rw [sub_eq_zero.mp first, sub_eq_zero.mp last] at formula
  rw [height_apply, real_inner_comm]
  change inner ℝ (K.normalSlope g) (b - a) + K.supportHeight f b - K.supportHeight f a = 0
  linarith

end Unfoldings.ConvexCap
