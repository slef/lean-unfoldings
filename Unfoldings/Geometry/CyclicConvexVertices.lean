module

public import Unfoldings.Geometry.ConeBoundaryRays

/-! The two edges at a convex polygon vertex suffice for a linear support test. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A cyclic list with positive corner turns and with every listed point on
the interior side of each oriented edge. -/
structure CyclicConvexVertices {I : Type*} (point : I → Plane) (next : Equiv.Perm I) : Prop where
  turn_pos : ∀ i, 0 < orient 0 (point i - point (next.symm i)) (point (next i) - point i)
  edge_support : ∀ i j, 0 ≤ orient (point i) (point (next i)) (point j)

/-- From a vertex, every other vertex lies between its two incident edges. -/
theorem CyclicConvexVertices.vertexDirection_mem_wedge {I : Type*}
    {point : I → Plane} {next : Equiv.Perm I} (convex : CyclicConvexVertices point next)
    (i j : I) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      point j - point i =
        s • (point (next i) - point i) + t • (point (next.symm i) - point i) := by
  let a := point (next i) - point i
  let b := point (next.symm i) - point i
  let v := point j - point i
  let d := orient 0 a b
  have d_pos : 0 < d := by
    have same : d = orient 0 (point i - point (next.symm i)) (point (next i) - point i) := by
      simp only [d, a, b, orient, PiLp.zero_apply, PiLp.sub_apply, sub_zero]
      ring
    rw [same]
    exact convex.turn_pos i
  have a_side : 0 ≤ orient 0 a v := by
    simpa only [a, v, orient, PiLp.zero_apply, PiLp.sub_apply, sub_zero] using
      convex.edge_support i j
  have b_side : 0 ≤ orient 0 v b := by
    have same : orient 0 v b = orient (point (next.symm i)) (point i) (point j) := by
      simp only [b, v, orient, PiLp.zero_apply, PiLp.sub_apply, sub_zero]
      ring
    rw [same]
    simpa only [next.apply_symm_apply] using convex.edge_support (next.symm i) j
  refine ⟨orient 0 v b / d, orient 0 a v / d, div_nonneg b_side d_pos.le,
    div_nonneg a_side d_pos.le, ?_⟩
  have h := congrArg (fun z : Plane => d⁻¹ • z) (orient_zero_balance a v b)
  simpa only [d, smul_add, smul_smul, div_eq_inv_mul, inv_mul_cancel₀ d_pos.ne', one_smul]
    using h

/-- Testing a form in the directions from one vertex to its two neighbors
proves that it is nonnegative in all directions from that vertex to the list. -/
theorem CyclicConvexVertices.nonneg_from_neighbors {I : Type*}
    {point : I → Plane} {next : Equiv.Perm I} (convex : CyclicConvexVertices point next)
    (i : I) (L : Plane →ₗ[ℝ] ℝ)
    (prev : 0 ≤ L (point (next.symm i) - point i))
    (succ : 0 ≤ L (point (next i) - point i)) (j : I) :
    0 ≤ L (point j - point i) := by
  obtain ⟨s, t, hs, ht, same⟩ := convex.vertexDirection_mem_wedge i j
  rw [same, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs succ) (mul_nonneg ht prev)

/-- Strict positivity at the two neighbors extends to each distinct vertex. -/
theorem CyclicConvexVertices.pos_from_neighbors {I : Type*}
    {point : I → Plane} {next : Equiv.Perm I} (convex : CyclicConvexVertices point next)
    (i : I) (L : Plane →ₗ[ℝ] ℝ)
    (prev : 0 < L (point (next.symm i) - point i))
    (succ : 0 < L (point (next i) - point i)) (j : I)
    (different : point j ≠ point i) :
    0 < L (point j - point i) := by
  obtain ⟨s, t, hs, ht, same⟩ := convex.vertexDirection_mem_wedge i j
  rw [same, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  by_cases sp : 0 < s
  · exact add_pos_of_pos_of_nonneg (mul_pos sp succ) (mul_nonneg ht prev.le)
  have sz : s = 0 := le_antisymm (le_of_not_gt sp) hs
  have tp : 0 < t := by
    by_contra absent
    have tz : t = 0 := le_antisymm (le_of_not_gt absent) ht
    exact different (sub_eq_zero.mp (by simpa only [sz, tz, zero_smul, add_zero] using same))
  exact add_pos_of_nonneg_of_pos (mul_nonneg hs succ.le) (mul_pos tp prev)

end Unfoldings
