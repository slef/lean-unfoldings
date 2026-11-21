module

public import Unfoldings.Geometry.RadialConeCoordinates

/-! The radial gauge extends each local chord-triangle plane to a global support. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Set

/-- A linear piece of a convex function on an open neighborhood supports
the function everywhere. -/
theorem linear_le_convex_of_eq_near {f : Space → ℝ} (convex : ConvexOn ℝ univ f)
    (L : Space →ₗ[ℝ] ℝ) {U : Set Space} (open_U : IsOpen U)
    (nonempty : U.Nonempty) (agree : ∀ x ∈ U, f x = L x) (x : Space) : L x ≤ f x := by
  obtain ⟨z, hz⟩ := nonempty
  obtain ⟨r, rpos, inside⟩ := Metric.mem_nhds_iff.mp (open_U.mem_nhds hz)
  let d := ‖x - z‖
  let t := min (r / (d + 1)) (1 / 2)
  have dn : 0 ≤ d := norm_nonneg _
  have tp : 0 < t := lt_min (by positivity) (by norm_num)
  have small : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have local_point : (1 - t) • z + t • x ∈ U := by
    apply inside
    rw [Metric.mem_ball, dist_eq_norm, show (1 - t) • z + t • x - z = t • (x - z) by module,
      norm_smul, Real.norm_eq_abs, abs_of_pos tp]
    change t * d < r
    have scaled : (r / (d + 1)) * d < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < d + 1)]
      nlinarith only [rpos]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) dn).trans_lt scaled
  have inequality := convex.2 (mem_univ z) (mem_univ x)
    (sub_nonneg.mpr small.le) tp.le (sub_add_cancel 1 t)
  rw [agree _ local_point, agree z hz] at inequality
  simp only [map_add, map_smul, smul_eq_mul] at inequality
  exact le_of_mul_le_mul_left (by linarith only [inequality]) tp

/-- Every full-dimensional radial triangle gives a genuine supporting plane
of the hull of all of the original radial sites. -/
theorem radialTriangle_supports_hull {I : Type*}
    (v : I → Fin 3 → Space) (cover : ∀ x, ∃ i, x ∈ radialTriangleCone (v i))
    (f : Space → ℝ) (convex : ConvexOn ℝ Set.univ f)
    (plane : I → Space →ₗ[ℝ] ℝ) (unit : ∀ i j, plane i (v i j) = 1)
    (agree : ∀ i x, x ∈ radialTriangleCone (v i) → f x = plane i x)
    (i : I) (independent : LinearIndependent ℝ (v i)) :
    ∀ x ∈ convexHull ℝ (insert 0 (range (fun ij : I × Fin 3 => v ij.1 ij.2))),
      plane i x ≤ 1 := by
  rw [convexHull_eq_sublevel_of_radial_triangles v cover f convex plane unit agree]
  intro x inside
  have h := linear_le_convex_of_eq_near convex (plane i) isOpen_interior
    (interior_radialTriangleCone_nonempty independent)
    (fun y hy => agree i y (interior_subset hy)) x
  exact h.trans inside

end Unfoldings
