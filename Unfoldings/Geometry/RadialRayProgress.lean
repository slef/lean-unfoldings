module

public import Unfoldings.Geometry.RadialChainProgress
public import Unfoldings.Geometry.PolygonalRayFrame
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! Quantitative radial inverses on whole polygonal rays, including the original infinite tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n) {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
  (margin : ∀ i, γ * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
    inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
  (tail_margin : γ * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
    inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)

include nonnegative small tail_margin in
theorem radial_tail_norm_progress (t s : ℝ≥0) (ordered : t ≤ s) :
    γ * ‖R.tail s - R.tail t‖ ≤ ‖R.tail s - R.start‖ - ‖R.tail t - R.start‖ := by
  have progress := norm_ray_progress (R.chain.vertex (Fin.last n) - R.start) R.direction
    nonnegative small t.coe_nonneg ordered tail_margin
  have point (r : ℝ≥0) : R.tail r - R.start =
      (R.chain.vertex (Fin.last n) - R.start) + (r : ℝ) • R.direction := by
    rw [tail]
    abel
  have difference : R.tail s - R.tail t = ((s : ℝ) - (t : ℝ)) • R.direction := by
    simp only [tail]
    module
  rw [difference, point s, point t]
  exact progress

include nonnegative small margin tail_margin in
theorem radial_prefix_tail_progress {x : E} (member : x ∈ Set.range R.chain.path) (t : ℝ≥0) :
    γ * ‖R.tail t - x‖ ≤ ‖R.tail t - R.start‖ - ‖x - R.start‖ := by
  apply radial_progress_trans R.start x (R.chain.vertex (Fin.last n)) (R.tail t) nonnegative
    (R.chain.radial_path_last_progress R.start nonnegative small margin member)
  simpa only [R.tail_zero] using
    R.radial_tail_norm_progress nonnegative small tail_margin 0 t zero_le

include nonnegative small margin tail_margin in
/-- The norm coordinate has the same quantitative inverse bound on all actual finite and
infinite bank points. No subdivision count appears in the constant. -/
theorem radial_carrier_inverse_bound {x y : E} (first : x ∈ R.carrier) (last : y ∈ R.carrier) :
    γ * ‖y - x‖ ≤ |‖y - R.start‖ - ‖x - R.start‖| := by
  rcases first with finite_first | ⟨t, rfl⟩ <;> rcases last with finite_last | ⟨s, rfl⟩
  · exact R.chain.radial_path_inverse_bound R.start nonnegative small margin
      finite_first finite_last
  · exact (R.radial_prefix_tail_progress nonnegative small margin tail_margin finite_first s).trans
      (le_abs_self _)
  · have bound :=
      (R.radial_prefix_tail_progress nonnegative small margin tail_margin finite_last t).trans
        (le_abs_self _)
    simpa only [norm_sub_rev, abs_sub_comm] using bound
  · rcases le_total t s with ordered | ordered
    · exact (R.radial_tail_norm_progress nonnegative small tail_margin t s ordered).trans
        (le_abs_self _)
    · have bound := (R.radial_tail_norm_progress nonnegative small tail_margin s t ordered).trans
        (le_abs_self _)
      simpa only [norm_sub_rev, abs_sub_comm] using bound

end Unfoldings.PolygonalRay

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

/-- The actual radial inverse is uniformly Lipschitz on whole edges and the infinite tail. -/
theorem lipschitz_radialPoint (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
      inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
    (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction) :
    LipschitzWith γ⁻¹ (R.radialPoint outward nonzero) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have bound := R.radial_carrier_inverse_bound γ.coe_nonneg small margin tail_margin
    (R.radialPoint_mem outward nonzero s) (R.radialPoint_mem outward nonzero r)
  rw [R.norm_radialPoint_sub_start, R.norm_radialPoint_sub_start] at bound
  have inverse : ‖R.radialPoint outward nonzero r - R.radialPoint outward nonzero s‖ ≤
      |(r : ℝ) - (s : ℝ)| / (γ : ℝ) :=
    (le_div_iff₀ (show (0 : ℝ) < γ from positive)).mpr
      (by simpa only [mul_comm] using bound)
  simpa only [dist_eq_norm, NNReal.dist_eq, NNReal.coe_inv, div_eq_inv_mul] using inverse

end Unfoldings.PolygonalRay
