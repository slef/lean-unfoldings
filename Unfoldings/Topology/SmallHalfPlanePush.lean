module

public import Unfoldings.Topology.HalfPlanePush
public import Mathlib.Topology.Algebra.ConstMulAction

/-! Compactly supported inward pushes in arbitrarily small half-plane charts. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

def halfPlaneOrigin : closedHalfPlane := ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩

def halfPlaneDilation (r : ℝ) (positive : 0 < r) : closedHalfPlane ≃ₜ closedHalfPlane :=
  (Homeomorph.smulOfNeZero r positive.ne' : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)).subtype (by
    intro p
    change 0 ≤ p.2 ↔ 0 ≤ r * p.2
    exact (mul_nonneg_iff_of_pos_left positive).symm)

@[simp] theorem halfPlaneDilation_apply (r : ℝ) (positive : 0 < r) (p : closedHalfPlane) :
    (halfPlaneDilation r positive p).val = r • p.val := rfl

@[simp] theorem halfPlaneDilation_origin (r : ℝ) (positive : 0 < r) :
    halfPlaneDilation r positive halfPlaneOrigin = halfPlaneOrigin := by
  apply Subtype.ext
  change r • (0 : ℝ × ℝ) = 0
  exact smul_zero r

theorem halfPlaneDilation_boundary_iff (r : ℝ) (positive : 0 < r) (p : closedHalfPlane) :
    p ∈ halfPlaneBoundary ↔ halfPlaneDilation r positive p ∈ halfPlaneBoundary := by
  change p.val.2 = 0 ↔ r * p.val.2 = 0
  exact (mul_eq_zero_iff_left positive.ne').symm

theorem dist_halfPlaneDilation_origin_le (r : ℝ) (positive : 0 < r)
    (p : closedHalfPlane) (inside : p ∈ pushSupport) :
    dist (halfPlaneDilation r positive p) halfPlaneOrigin ≤ r := by
  change dist (r • p.val) (0 : ℝ × ℝ) ≤ r
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  change max |r * p.val.1 - 0| |r * p.val.2 - 0| ≤ r
  have vertical : 0 ≤ p.val.2 := p.property
  simp only [sub_zero, abs_mul, abs_of_pos positive, abs_of_nonneg vertical]
  exact max_le (by nlinarith [inside.1]) (by nlinarith [inside.2])

/-- An inward push can be supported in any prescribed half-plane neighborhood. -/
theorem exists_smallHalfPlanePush (U : Set closedHalfPlane) (open_U : IsOpen U)
    (center : halfPlaneOrigin ∈ U) :
    Nonempty (BoundaryPush.Local (B := halfPlaneBoundary) U halfPlaneOrigin) := by
  obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp open_U halfPlaneOrigin center
  let r := ε / 2
  have rpos : 0 < r := half_pos positive
  let d := halfPlaneDilation r rpos
  let f := standardBoundaryPush.transport halfPlaneBoundary d
    (halfPlaneDilation_boundary_iff r rpos)
  let K := d '' pushSupport
  let W := d '' pushRectangle
  have supported : K ⊆ U := by
    rintro _ ⟨p, hp, rfl⟩
    apply ball
    exact (dist_halfPlaneDilation_origin_le r rpos p hp).trans_lt (by dsimp [r]; linarith)
  have W_subset_K : W ⊆ K := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, ⟨hp.1.le, hp.2.le⟩, rfl⟩
  refine ⟨⟨f, K, isCompact_pushSupport.image d.continuous, supported, ?_, ?_,
    W, d.isOpenMap _ isOpen_pushRectangle, ?_, W_subset_K.trans supported, ?_⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨inwardPush p, inwardPush_mapsTo_support hp, ?_⟩
    change d (inwardPush p) = d (inwardPush (d.symm (d p)))
    rw [Homeomorph.symm_apply_apply]
  · intro p outside
    have original : d.symm p ∉ pushSupport := by
      intro inside
      exact outside ⟨d.symm p, inside, d.apply_symm_apply p⟩
    change d (inwardPush (d.symm p)) = p
    rw [inwardPush_fixed_of_not_mem_support _ original, Homeomorph.apply_symm_apply]
  · refine ⟨halfPlaneOrigin, ?_, halfPlaneDilation_origin r rpos⟩
    change |(0 : ℝ)| < 1 ∧ (0 : ℝ) < 1
    norm_num
  · rintro _ ⟨⟨p, hp, rfl⟩, boundary⟩
    refine ⟨boundary, ?_⟩
    have source_boundary := (halfPlaneDilation_boundary_iff r rpos p).mpr boundary
    have pushed : inwardPush p ∉ halfPlaneBoundary :=
      ((inwardPush_boundary_positive p source_boundary).mpr hp.1).ne'
    change d (inwardPush (d.symm (d p))) ∉ halfPlaneBoundary
    rw [Homeomorph.symm_apply_apply]
    exact mt (halfPlaneDilation_boundary_iff r rpos _).mpr pushed

end Unfoldings.PlanarTopology
