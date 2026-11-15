module

public import Unfoldings.Geometry.PolygonalBankTailGerm
public import Unfoldings.Geometry.RayInteriorDirections

/-! Exact original unbounded-tail germs and strict radial progress, beyond the final bend. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

include outward nonzero

/-- A positive original tail point is beyond every point of the entire finite prefix. -/
theorem tail_point_not_mem_prefix (t : ℝ≥0) (positive : 0 < t) :
    R.tail t ∉ Set.range R.chain.path := by
  intro member
  have before := R.prefix_radius_le outward member
  have after := R.tail_radius_strictMono outward nonzero positive
  dsimp only at after
  rw [R.tail_zero] at after
  exact (not_lt_of_ge before) after

/-- A positive original tail point has strict radial progress even when the bend's initial
tail margin is zero. No nondegeneracy assumptions on finite edges are needed. -/
theorem inner_tail_point_pos (t : ℝ≥0) (positive : 0 < t) :
    0 < inner ℝ (R.tail t - R.start) R.direction := by
  have initial := outward.2
  have forward := mul_pos (show (0 : ℝ) < t from positive)
    (sq_pos_of_pos (norm_pos_iff.mpr nonzero))
  have difference : R.tail t - R.start =
      (R.chain.vertex (Fin.last n) - R.start) + (t : ℝ) • R.direction := by
    rw [tail]
    abel
  rw [difference, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith

end Unfoldings.PolygonalRay

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Beyond the last finite vertex the exact bank directions are the whole original tail
line. This uses the entire unbounded tail, allowing arbitrary finite-edge degeneracies. -/
theorem complexCarrierGerm_tail_point (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (t : ℝ≥0) (positive : 0 < t) :
    R.complexCarrierGerm (R.tail t) =
      nonnegativeRay (-R.direction) ∪ nonnegativeRay R.direction := by
  have no_prefix : ∀ᶠ z in 𝓝 (R.tail t), z ∉ Set.range R.chain.path :=
    (isCompact_range R.chain.path.continuous).isClosed.isOpen_compl.mem_nhds
      (R.tail_point_not_mem_prefix outward nonzero t positive)
  have tail_model := eventually_mem_ray_iff_direction_line_normed
    (R.chain.vertex (Fin.last n)) R.direction nonzero t positive
  have near : ∀ᶠ z in 𝓝 (R.tail t), z ∈ R.carrier ↔
      z - R.tail t ∈ nonnegativeRay (-R.direction) ∪ nonnegativeRay R.direction := by
    filter_upwards [no_prefix, tail_model] with z prefix_absent model
    rw [carrier]
    simp only [Set.mem_union, prefix_absent, false_or, R.mem_range_tail_iff_ray]
    rw [model, range_smul_eq_nonnegativeRays, Set.union_comm]
    rfl
  apply eq_of_local_homogeneous_models (R.tail t)
    (fun v _r positive => R.mem_complexCarrierGerm_smul_iff _ v positive) _
    (R.eventually_mem_carrier_iff_complexGerm _) near
  intro v r positive
  simp only [Set.mem_union, mem_nonnegativeRay_smul_iff _ _ positive]

end Unfoldings.PolygonalRay
