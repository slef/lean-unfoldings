module

public import Unfoldings.Geometry.ConeBoundaryRays
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation

/-! A finite test that a polygonal convex hull contains a closed disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductSpace

private def clockwiseQuarterTurn (x : Plane) : Plane := WithLp.toLp 2 ![x 1, -x 0]

private theorem norm_clockwiseQuarterTurn (x : Plane) : ‖clockwiseQuarterTurn x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, clockwiseQuarterTurn,
    Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq]
  ring

private theorem inner_plane_formula (x y : Plane) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Consecutive strictly left turns and lower bounds on the edge distances
certify the inradius of the convex hull. At a supporting vertex, the support
direction is in the cone of the two adjacent outward normals. -/
theorem closedBall_subset_convexHull_of_edge_distances {I : Type*} [Finite I] [Nonempty I]
    (p : I → Plane) (next : Equiv.Perm I) {r : ℝ} (radius_nonnegative : 0 ≤ r)
    (turn : ∀ i, 0 < orient 0 (p i - p (next.symm i)) (p (next i) - p i))
    (distance : ∀ i, r * ‖p (next i) - p i‖ ≤ orient 0 (p i) (p (next i))) :
    Metric.closedBall (0 : Plane) r ⊆ convexHull ℝ (Set.range p) := by
  classical
  let := Fintype.ofFinite I
  intro x member
  have radius : ‖x‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using member
  by_contra outside
  have compact : IsCompact (convexHull ℝ (Set.range p)) :=
    (Set.finite_range p).isCompact_convexHull ℝ
  obtain ⟨L, q, support, above⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) compact.isClosed outside
  let u : Plane := (toDual ℝ Plane).symm L
  have eq (y : Plane) : inner ℝ u y = L y := by simp only [u, toDual_symm_apply]
  obtain ⟨i, _, max_at⟩ := Finset.exists_max_image (Finset.univ : Finset I)
    (fun k => inner ℝ u (p k)) Finset.univ_nonempty
  let a := p i - p (next.symm i)
  let b := p (next i) - p i
  let A := clockwiseQuarterTurn a
  let B := clockwiseQuarterTurn b
  let det := orient 0 A B
  have det_pos : 0 < det := by
    have identity : det = orient 0 a b := by
      simp only [det, A, B, clockwiseQuarterTurn, orient, PiLp.zero_apply, sub_zero]
      change a 1 * (-b 0) - (-a 0) * b 1 = a 0 * b 1 - a 1 * b 0
      ring
    rw [identity]
    exact turn i
  let α := orient 0 u B / det
  let β := orient 0 A u / det
  have α_nonneg : 0 ≤ α := by
    apply div_nonneg _ det_pos.le
    have identity : orient 0 u B = -inner ℝ u b := by
      rw [inner_plane_formula]
      simp only [B, clockwiseQuarterTurn, orient, PiLp.zero_apply, sub_zero]
      change u 0 * (-b 0) - u 1 * b 1 = _
      ring
    rw [identity, neg_nonneg, show b = p (next i) - p i from rfl, inner_sub_right, sub_nonpos]
    exact max_at (next i) (Finset.mem_univ _)
  have β_nonneg : 0 ≤ β := by
    apply div_nonneg _ det_pos.le
    have identity : orient 0 A u = inner ℝ u a := by
      rw [inner_plane_formula]
      simp only [A, clockwiseQuarterTurn, orient, PiLp.zero_apply, sub_zero]
      change a 1 * u 1 - (-a 0) * u 0 = _
      ring
    rw [identity, show a = p i - p (next.symm i) from rfl, inner_sub_right, sub_nonneg]
    exact max_at (next.symm i) (Finset.mem_univ _)
  have represented : α • A + β • B = u := by
    have balance := orient_zero_balance A u B
    have h := congrArg (fun v : Plane => det⁻¹ • v) balance
    simpa only [det, α, β, smul_add, smul_smul, div_eq_inv_mul,
      inv_mul_cancel₀ det_pos.ne', one_smul] using h.symm
  have norm_bound : ‖u‖ ≤ α * ‖A‖ + β * ‖B‖ := by
    rw [← represented]
    exact (norm_add_le _ _).trans_eq (by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg α_nonneg,
        abs_of_nonneg β_nonneg])
  have a_offset : inner ℝ A (p i) = orient 0 (p (next.symm i)) (p i) := by
    rw [inner_plane_formula]
    simp only [A, clockwiseQuarterTurn, a, orient, PiLp.zero_apply, sub_zero, PiLp.sub_apply]
    change (p i 1 - p (next.symm i) 1) * p i 0 +
      -(p i 0 - p (next.symm i) 0) * p i 1 = _
    ring
  have b_offset : inner ℝ B (p i) = orient 0 (p i) (p (next i)) := by
    rw [inner_plane_formula]
    simp only [B, clockwiseQuarterTurn, b, orient, PiLp.zero_apply, sub_zero, PiLp.sub_apply]
    change (p (next i) 1 - p i 1) * p i 0 + -(p (next i) 0 - p i 0) * p i 1 = _
    ring
  have left : r * ‖A‖ ≤ inner ℝ A (p i) := by
    rw [a_offset, norm_clockwiseQuarterTurn]
    simpa only [a, next.apply_symm_apply] using distance (next.symm i)
  have right : r * ‖B‖ ≤ inner ℝ B (p i) := by
    rw [b_offset, norm_clockwiseQuarterTurn]
    exact distance i
  have inside_support : r * ‖u‖ ≤ inner ℝ u (p i) := calc
    _ ≤ r * (α * ‖A‖ + β * ‖B‖) := mul_le_mul_of_nonneg_left norm_bound radius_nonnegative
    _ = α * (r * ‖A‖) + β * (r * ‖B‖) := by ring
    _ ≤ α * inner ℝ A (p i) + β * inner ℝ B (p i) :=
      add_le_add (mul_le_mul_of_nonneg_left left α_nonneg)
        (mul_le_mul_of_nonneg_left right β_nonneg)
    _ = _ := by rw [← represented, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have x_support : inner ℝ u x ≤ r * ‖u‖ := calc
    _ ≤ ‖u‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * r := mul_le_mul_of_nonneg_left radius (norm_nonneg _)
    _ = _ := mul_comm _ _
  have bound := support (p i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
  rw [← eq] at above bound
  exact (not_lt_of_ge ((x_support.trans inside_support).trans bound.le)) above

end Unfoldings
