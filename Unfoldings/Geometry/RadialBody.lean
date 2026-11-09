module

public import Unfoldings.Geometry.RadialInterior
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UnitInterval

/-!
# Compact regions with strictly interior radial contractions

These hypotheses are proved for the constructed source domain. No convexity
is imposed: nonconvex nets are allowed. Every ray has exactly one boundary
point, and radial normalization identifies the boundary with the unit sphere.
-/

@[expose] public section

open scoped Topology

noncomputable section

namespace Unfoldings

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure RadialBody where
  carrier : Set E
  compact : IsCompact carrier
  zero_interior : (0 : E) ∈ interior carrier
  radial_interior : ∀ x ∈ carrier, ∀ t : unitInterval, t < 1 →
    (t : ℝ) • x ∈ interior carrier

namespace RadialBody

variable {E} (B : RadialBody E)

theorem boundary_mem (x : frontier B.carrier) : x.val ∈ B.carrier :=
  B.compact.isClosed.frontier_subset x.property

theorem boundary_not_interior (x : frontier B.carrier) : x.val ∉ interior B.carrier :=
  (mem_frontier_iff_notMem_interior (B.boundary_mem x)).mp x.property

theorem boundary_ne_zero (x : frontier B.carrier) : x.val ≠ 0 := by
  intro equal
  exact B.boundary_not_interior x (equal ▸ B.zero_interior)

def boundaryDirection (x : frontier B.carrier) : Metric.sphere (0 : E) 1 :=
  ⟨‖x.val‖⁻¹ • x.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (B.boundary_ne_zero x)⟩

theorem norm_smul_boundaryDirection (x : frontier B.carrier) :
    ‖x.val‖ • (B.boundaryDirection x).val = x.val := by
  change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (B.boundary_ne_zero x)), one_smul]

theorem boundaryDirection_injective : Function.Injective B.boundaryDirection := by
  intro x y equal
  have value_equal := congrArg Subtype.val equal
  have no_less (a b : frontier B.carrier)
      (direction : (B.boundaryDirection a).val = (B.boundaryDirection b).val) :
      ¬ ‖a.val‖ < ‖b.val‖ := by
    intro less
    have positive : 0 < ‖b.val‖ := norm_pos_iff.mpr (B.boundary_ne_zero b)
    let t : unitInterval := ⟨‖a.val‖ / ‖b.val‖, div_nonneg (norm_nonneg _) positive.le,
      (div_le_one positive).mpr less.le⟩
    have before : t < 1 := (div_lt_one positive).mpr less
    have expression : (t : ℝ) • b.val = a.val := by
      rw [← B.norm_smul_boundaryDirection b, smul_smul, div_mul_cancel₀ _ positive.ne',
        ← direction, B.norm_smul_boundaryDirection]
    have inside := B.radial_interior b.val (B.boundary_mem b) t before
    rw [expression] at inside
    exact B.boundary_not_interior a inside
  have norms : ‖x.val‖ = ‖y.val‖ :=
    le_antisymm (le_of_not_gt (no_less y x value_equal.symm))
      (le_of_not_gt (no_less x y value_equal))
  apply Subtype.ext
  rw [← B.norm_smul_boundaryDirection x, ← B.norm_smul_boundaryDirection y, norms, value_equal]

theorem continuous_boundaryDirection : Continuous B.boundaryDirection :=
  ((continuous_subtype_val.norm.inv₀
    (fun x => norm_ne_zero_iff.mpr (B.boundary_ne_zero x))).smul
      continuous_subtype_val).subtype_mk _

theorem exists_ray_boundary (u : E) (unit : ‖u‖ = 1) :
    ∃ r : ℝ, 0 < r ∧ r • u ∈ frontier B.carrier := by
  obtain ⟨M, _positive_M, bound⟩ := B.compact.isBounded.exists_pos_norm_le
  let T : Set ℝ := {r | 0 ≤ r ∧ r • u ∈ B.carrier}
  have closed : IsClosed T := isClosed_Ici.inter
    (B.compact.isClosed.preimage (continuous_id.smul continuous_const))
  have bounded : T ⊆ Set.Icc 0 M := by
    intro r hr
    refine ⟨hr.1, ?_⟩
    have estimate := bound (r • u) hr.2
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1, unit, mul_one] using estimate
  have compact : IsCompact T := isCompact_Icc.of_isClosed_subset closed bounded
  have nonempty : T.Nonempty := ⟨0, le_rfl, by
    simpa only [zero_smul] using interior_subset B.zero_interior⟩
  obtain ⟨r, member, maximal⟩ := compact.exists_isMaxOn nonempty continuous_id.continuousOn
  obtain ⟨δ, positive_δ, interior_ball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior 0 B.zero_interior
  have ball := interior_ball.trans interior_subset
  have small_member : δ / 2 ∈ T := by
    refine ⟨(half_pos positive_δ).le, ball ?_⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos positive_δ), unit, mul_one]
    linarith
  have positive : 0 < r := (half_pos positive_δ).trans_le (maximal small_member)
  refine ⟨r, positive, (mem_frontier_iff_notMem_interior member.2).mpr ?_⟩
  intro inside
  obtain ⟨t, after, in_body⟩ := exists_gt_one_smul_mem_of_interior inside
  have longer_member : t * r ∈ T :=
    ⟨mul_nonneg (by linarith) positive.le, by simpa only [mul_smul] using in_body⟩
  have impossible := maximal longer_member
  change t * r ≤ r at impossible
  nlinarith

theorem boundaryDirection_surjective : Function.Surjective B.boundaryDirection := by
  intro u
  obtain ⟨r, positive, boundary⟩ := B.exists_ray_boundary u.val
    (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)
  refine ⟨⟨r • u.val, boundary⟩, ?_⟩
  apply Subtype.ext
  change ‖r • u.val‖⁻¹ • (r • u.val) = u.val
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos positive,
    (show ‖u.val‖ = 1 by simpa only [Metric.mem_sphere, dist_zero_right] using u.property),
    mul_one, smul_smul,
    inv_mul_cancel₀ positive.ne', one_smul]

def boundaryHomeomorph : frontier B.carrier ≃ₜ Metric.sphere (0 : E) 1 := by
  let := isCompact_iff_compactSpace.mp
    (B.compact.of_isClosed_subset isClosed_frontier B.compact.isClosed.frontier_subset)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective B.boundaryDirection
      ⟨B.boundaryDirection_injective, B.boundaryDirection_surjective⟩)
    B.continuous_boundaryDirection

end RadialBody
end Unfoldings
