module

public import Unfoldings.Roof.ClosingGraphSegments

/-! All actual straight contacts of the two-link closing graph share the sharp tilt budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real PlanarTopology

universe u v

private theorem horizontal_mem_Icc_of_mem_segment {p q z : Plane} (order : p 0 ≤ q 0)
    (member : z ∈ segment ℝ p q) : z 0 ∈ Set.Icc (p 0) (q 0) := by
  obtain ⟨t, interval, rfl⟩ := (segment_eq_image_lineMap ℝ p q).subset member
  rw [AffineMap.lineMap_apply_module']
  change p 0 ≤ t * (q 0 - p 0) + p 0 ∧ t * (q 0 - p 0) + p 0 ≤ q 0
  exact ⟨by linarith only [mul_nonneg interval.1 (sub_nonneg.mpr order)], by
    linarith only [mul_nonneg (sub_nonneg.mpr interval.2) (sub_nonneg.mpr order)]⟩

private theorem horizontal_mem_Ioo_of_mem_openSegment {p q z : Plane} (order : p 0 < q 0)
    (member : z ∈ openSegment ℝ p q) : z 0 ∈ Set.Ioo (p 0) (q 0) := by
  obtain ⟨t, interval, rfl⟩ := (openSegment_eq_image_lineMap ℝ p q).subset member
  rw [AffineMap.lineMap_apply_module']
  change p 0 < t * (q 0 - p 0) + p 0 ∧ t * (q 0 - p 0) + p 0 < q 0
  exact ⟨by linarith only [mul_pos interval.1 (sub_pos.mpr order)], by
    linarith only [mul_pos (sub_pos.mpr interval.2) (sub_pos.mpr order)]⟩

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

private theorem closingErrors_le_of_join {I J : Type*} [Fintype I] [Fintype J]
    {faces : Set Face} {p c d e : Plane} {length : ℝ} (join : p + length • d = c)
    (d_unit : ‖d‖ = 1) (e_unit : ‖e‖ = 1) (middle : Face)
    (active : K.supportHeight middle c = K.roofHeight c)
    (first : K.RegularClosingLink faces p d I)
    (last : K.RegularClosingLink faces c e J)
    (before : ∀ i, first.time i < length) (after : ∀ j, 0 < last.time j)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    (∑ i, |K.restrictedBoundaryTurnError faces (first.bank i)|) +
      (∑ j, |K.restrictedBoundaryTurnError faces (last.bank j)|) ≤
      sin φ * (2 * φ + tan φ * ‖d - e‖) := by
  subst c
  exact K.sum_abs_restricted_closing_errors_le p d e d_unit e_unit length middle active
    first last before after nonnegative small tilt

set_option maxHeartbeats 1700000 in
open Classical in
/-- The true regional angles at all strict contacts of both closing links
pay at most twice the tilt times its sine, plus the direction mismatch cost. -/
theorem sum_abs_graphClosingLink_excess_le {f : ℝ → ℝ} (hf : Continuous f)
    {p c q : Plane} (first_progress : p 0 < c 0) (last_progress : c 0 < q 0)
    (trace : graphPoint f '' Set.Icc (p 0) (q 0) = segment ℝ p c ∪ segment ℝ c q)
    (inside : graphPoint f '' Set.Icc (p 0) (q 0) ⊆ interior K.footprint)
    (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ p 0 ∧ z 0 ≠ q 0)
    (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier)
      (graphPoint f '' Set.Icc (p 0) (q 0)))
    (first_regular : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ openSegment ℝ p c →
      K.HasRegularSectionSlopes w (c - p))
    (last_regular : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ openSegment ℝ c q →
      K.HasRegularSectionSlopes w (q - c))
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    let U := facesAboveGraph sample f (p 0) (q 0)
    let I := {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ p c}
    let J := {w : C.Vertex Set.univ // K.projectedVertex w ∈ openSegment ℝ c q}
    (∑ i : I, |K.regionalAngleExcess U i.val|) + (∑ j : J, |K.regionalAngleExcess U j.val|) ≤
      sin φ * (2 * φ + tan φ * ‖NormedSpace.normalize (c - p) - NormedSpace.normalize (q - c)‖) := by
  let d := NormedSpace.normalize (c - p)
  let e := NormedSpace.normalize (q - c)
  have d_ne : c - p ≠ 0 := sub_ne_zero.mpr
    (fun h => first_progress.ne (congrArg (fun x : Plane => x 0) h.symm))
  have e_ne : q - c ≠ 0 := sub_ne_zero.mpr
    (fun h => last_progress.ne (congrArg (fun x : Plane => x 0) h.symm))
  have closed_segment (x y : Plane) : IsClosed (segment ℝ x y) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  have first_disjoint : Disjoint (openSegment ℝ p c) (segment ℝ c q) := by
    apply Set.disjoint_left.mpr
    intro z first last
    exact (not_lt_of_ge (horizontal_mem_Icc_of_mem_segment last_progress.le last).1)
      (horizontal_mem_Ioo_of_mem_openSegment first_progress first).2
  have last_disjoint : Disjoint (openSegment ℝ c q) (segment ℝ p c) := by
    apply Set.disjoint_left.mpr
    intro z last first
    exact (not_lt_of_ge (horizontal_mem_Icc_of_mem_segment first_progress.le first).2)
      (horizontal_mem_Ioo_of_mem_openSegment last_progress last).1
  obtain ⟨first, before, first_error⟩ :=
    K.exists_regularClosingLink_on_graphSegment hf sample sample_in endpoints aligned inside
      first_progress le_rfl last_progress.le (fun _ hx => trace.symm.subset (Or.inl hx))
      (segment ℝ c q) (closed_segment c q) trace.subset first_disjoint first_regular
  obtain ⟨last, after, last_error⟩ :=
    K.exists_regularClosingLink_on_graphSegment hf sample sample_in endpoints aligned inside
      last_progress first_progress.le le_rfl (fun _ hx => trace.symm.subset (Or.inr hx))
      (segment ℝ p c) (closed_segment p c) (by rw [trace, Set.union_comm])
      last_disjoint last_regular
  have join : p + ‖c - p‖ • d = c := by
    change p + ‖c - p‖ • NormedSpace.normalize (c - p) = c
    rw [NormedSpace.norm_smul_normalize]
    abel
  obtain ⟨middle, active⟩ := K.exists_roofHeight_eq_supportHeight c
  have estimate := K.closingErrors_le_of_join join (NormedSpace.norm_normalize d_ne)
    (NormedSpace.norm_normalize e_ne) middle active.symm first last
    (fun i => (before i).2) (fun j => (after j).1) nonnegative small tilt
  simp only [first_error, last_error, abs_neg] at estimate
  exact estimate

end Unfoldings.ConvexRoof
