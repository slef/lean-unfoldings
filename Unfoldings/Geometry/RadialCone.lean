module

public import Unfoldings.Geometry.RadialBody
public import Unfoldings.Topology.CommonFibers

/-!
# Radial bodies are closed balls

Both the body and the closed unit ball are quotients of its boundary times
the unit interval. Radial normalization proves that the two quotient maps
have exactly the same fibers. This constructs a homeomorphism, including at
the common collapsed center, without any convexity assumption.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.RadialBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : RadialBody E)

def unitDirection (x : E) (nonzero : x ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨‖x‖⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr nonzero⟩

theorem norm_smul_unitDirection (x : E) (nonzero : x ≠ 0) :
    ‖x‖ • (unitDirection x nonzero).val = x := by
  change ‖x‖ • (‖x‖⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzero), one_smul]

theorem boundary_nonempty [Nontrivial E] : (frontier B.carrier).Nonempty := by
  obtain ⟨x, nonzero⟩ := exists_ne (0 : E)
  let u := unitDirection x nonzero
  obtain ⟨r, _positive, boundary⟩ := B.exists_ray_boundary u.val
    (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)
  exact ⟨r • u.val, boundary⟩

theorem smul_mem (t : unitInterval) {x : E} (inside : x ∈ B.carrier) :
    (t : ℝ) • x ∈ B.carrier := by
  by_cases full : t = 1
  · simpa only [full, Set.Icc.coe_one, one_smul] using inside
  · exact interior_subset (B.radial_interior x inside t (lt_of_le_of_ne t.property.2 full))

abbrev Cone := frontier B.carrier × unitInterval

def coneToBody (x : B.Cone) : B.carrier :=
  ⟨(x.2 : ℝ) • x.1.val, B.smul_mem x.2 (B.boundary_mem x.1)⟩

def coneToBall (x : B.Cone) : Metric.closedBall (0 : E) 1 :=
  ⟨(x.2 : ℝ) • (B.boundaryDirection x.1).val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg x.2.property.1,
      (show ‖(B.boundaryDirection x.1).val‖ = 1 by
        simpa only [Metric.mem_sphere, dist_zero_right] using (B.boundaryDirection x.1).property),
      mul_one]
    exact x.2.property.2⟩

theorem continuous_coneToBody : Continuous B.coneToBody :=
  ((continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)).subtype_mk _

theorem continuous_coneToBall : Continuous B.coneToBall :=
  ((continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp (B.continuous_boundaryDirection.comp continuous_fst))).subtype_mk _

theorem coneToBody_surjective [Nontrivial E] : Function.Surjective B.coneToBody := by
  intro x
  by_cases zero : x.val = 0
  · obtain ⟨b, boundary⟩ := B.boundary_nonempty
    exact ⟨(⟨b, boundary⟩, 0), Subtype.ext (by simpa only [coneToBody, Set.Icc.coe_zero,
      zero_smul] using zero.symm)⟩
  · let u := unitDirection x.val zero
    obtain ⟨r, positive, boundary⟩ := B.exists_ray_boundary u.val
      (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)
    have expression : ‖x.val‖ • u.val = x.val := norm_smul_unitDirection _ _
    have bounded : ‖x.val‖ ≤ r := by
      by_contra wrong
      have less : r < ‖x.val‖ := lt_of_not_ge wrong
      have positive_norm : 0 < ‖x.val‖ := norm_pos_iff.mpr zero
      let t : unitInterval := ⟨r / ‖x.val‖, div_nonneg positive.le positive_norm.le,
        (div_le_one positive_norm).mpr less.le⟩
      have before : t < 1 := (div_lt_one positive_norm).mpr less
      have scaled : (t : ℝ) • x.val = r • u.val := by
        rw [← expression, smul_smul, div_mul_cancel₀ _ positive_norm.ne']
      have inside := B.radial_interior x.val x.property t before
      rw [scaled] at inside
      exact (B.boundary_not_interior ⟨r • u.val, boundary⟩) inside
    let t : unitInterval := ⟨‖x.val‖ / r, div_nonneg (norm_nonneg _) positive.le,
      (div_le_one positive).mpr bounded⟩
    refine ⟨(⟨r • u.val, boundary⟩, t), Subtype.ext ?_⟩
    change (‖x.val‖ / r) • (r • u.val) = x.val
    rw [smul_smul, div_mul_cancel₀ _ positive.ne', expression]

theorem coneToBall_surjective [Nontrivial E] : Function.Surjective B.coneToBall := by
  intro x
  by_cases zero : x.val = 0
  · obtain ⟨b, boundary⟩ := B.boundary_nonempty
    exact ⟨(⟨b, boundary⟩, 0), Subtype.ext (by simpa only [coneToBall, Set.Icc.coe_zero,
      zero_smul] using zero.symm)⟩
  · let u := unitDirection x.val zero
    let b := B.boundaryHomeomorph.symm u
    let t : unitInterval := ⟨‖x.val‖, norm_nonneg _, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
    refine ⟨(b, t), Subtype.ext ?_⟩
    have equal : B.boundaryDirection b = u := B.boundaryHomeomorph.apply_symm_apply u
    change ‖x.val‖ • (B.boundaryDirection b).val = x.val
    rw [equal]
    exact norm_smul_unitDirection _ _

theorem normalize_smul_pos (x : E) {t : ℝ} (positive : 0 < t) :
    ‖t • x‖⁻¹ • (t • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos positive, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ positive.ne', mul_one]

theorem cone_common_fibers (a b : B.Cone) :
    B.coneToBody a = B.coneToBody b ↔ B.coneToBall a = B.coneToBall b := by
  constructor
  · intro equal
    have value_equal := congrArg Subtype.val equal
    change (a.2 : ℝ) • a.1.val = (b.2 : ℝ) • b.1.val at value_equal
    by_cases zero : (a.2 : ℝ) = 0
    · have other_zero : (b.2 : ℝ) = 0 := by
        have vanished : (b.2 : ℝ) • b.1.val = 0 := by rw [← value_equal, zero, zero_smul]
        exact (smul_eq_zero.mp vanished).resolve_right (B.boundary_ne_zero b.1)
      apply Subtype.ext
      simp only [coneToBall, zero, other_zero, zero_smul]
    · have other_zero : (b.2 : ℝ) ≠ 0 := by
        intro wrong
        rw [wrong, zero_smul] at value_equal
        exact (smul_ne_zero zero (B.boundary_ne_zero a.1)) value_equal
      have directions : B.boundaryDirection a.1 = B.boundaryDirection b.1 := by
        apply Subtype.ext
        change ‖a.1.val‖⁻¹ • a.1.val = ‖b.1.val‖⁻¹ • b.1.val
        have normalized := congrArg (fun x : E => ‖x‖⁻¹ • x) value_equal
        simpa only [normalize_smul_pos _ (lt_of_le_of_ne a.2.property.1 (Ne.symm zero)),
          normalize_smul_pos _ (lt_of_le_of_ne b.2.property.1 (Ne.symm other_zero))]
          using normalized
      have boundary_equal := B.boundaryDirection_injective directions
      have times : (a.2 : ℝ) = (b.2 : ℝ) := by
        rw [boundary_equal] at value_equal
        exact smul_left_injective ℝ (B.boundary_ne_zero b.1) value_equal
      apply Subtype.ext
      change (a.2 : ℝ) • (B.boundaryDirection a.1).val =
        (b.2 : ℝ) • (B.boundaryDirection b.1).val
      rw [directions, times]
  · intro equal
    have value_equal := congrArg Subtype.val equal
    have times : (a.2 : ℝ) = (b.2 : ℝ) := by
      have norms := congrArg norm value_equal
      simpa only [coneToBall, norm_smul, Real.norm_eq_abs, abs_of_nonneg a.2.property.1,
        abs_of_nonneg b.2.property.1,
        (show ‖(B.boundaryDirection a.1).val‖ = 1 by
          simpa only [Metric.mem_sphere, dist_zero_right] using (B.boundaryDirection a.1).property),
        (show ‖(B.boundaryDirection b.1).val‖ = 1 by
          simpa only [Metric.mem_sphere, dist_zero_right] using (B.boundaryDirection b.1).property),
        mul_one] using norms
    by_cases zero : (a.2 : ℝ) = 0
    · apply Subtype.ext
      simp only [coneToBody, ← times, zero, zero_smul]
    · have directions : B.boundaryDirection a.1 = B.boundaryDirection b.1 := by
        apply Subtype.ext
        change (a.2 : ℝ) • (B.boundaryDirection a.1).val =
          (b.2 : ℝ) • (B.boundaryDirection b.1).val at value_equal
        rw [← times] at value_equal
        exact (smul_right_injective E zero) value_equal
      have boundary_equal := B.boundaryDirection_injective directions
      apply Subtype.ext
      change (a.2 : ℝ) • a.1.val = (b.2 : ℝ) • b.1.val
      rw [times, boundary_equal]

def closedBallHomeomorph [Nontrivial E] :
    B.carrier ≃ₜ Metric.closedBall (0 : E) 1 := by
  let := isCompact_iff_compactSpace.mp
    (B.compact.of_isClosed_subset isClosed_frontier B.compact.isClosed.frontier_subset)
  exact homeomorphOfCompactCommonFibers B.coneToBody B.coneToBall
    B.continuous_coneToBody B.continuous_coneToBall
    B.coneToBody_surjective B.coneToBall_surjective B.cone_common_fibers

theorem closedBallHomeomorph_cone [Nontrivial E] (x : B.Cone) :
    B.closedBallHomeomorph (B.coneToBody x) = B.coneToBall x := by
  let := isCompact_iff_compactSpace.mp
    (B.compact.of_isClosed_subset isClosed_frontier B.compact.isClosed.frontier_subset)
  exact homeomorphOfCompactCommonFibers_apply B.coneToBody B.coneToBall
    B.continuous_coneToBody B.continuous_coneToBall
    B.coneToBody_surjective B.coneToBall_surjective B.cone_common_fibers x

theorem closedBallHomeomorph_boundary [Nontrivial E] (x : frontier B.carrier) :
    (B.closedBallHomeomorph ⟨x.val, B.boundary_mem x⟩).val = (B.boundaryDirection x).val := by
  have equal := congrArg Subtype.val (B.closedBallHomeomorph_cone (x, 1))
  simpa only [coneToBody, coneToBall, Set.Icc.coe_one, one_smul] using equal

theorem closedBallHomeomorph_boundary_iff [Nontrivial E] (x : B.carrier) :
    (B.closedBallHomeomorph x).val ∈ Metric.sphere (0 : E) 1 ↔ x.val ∈ frontier B.carrier := by
  constructor
  · obtain ⟨⟨b, t⟩, rfl⟩ := B.coneToBody_surjective x
    rw [B.closedBallHomeomorph_cone]
    intro on_sphere
    have time_eq : (t : ℝ) = 1 := by
      simpa only [coneToBall, Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg t.property.1,
        (show ‖(B.boundaryDirection b).val‖ = 1 by
          simpa only [Metric.mem_sphere, dist_zero_right] using (B.boundaryDirection b).property),
        mul_one] using on_sphere
    change (t : ℝ) • b.val ∈ frontier B.carrier
    simpa only [time_eq, one_smul] using b.property
  · intro boundary
    rw [B.closedBallHomeomorph_boundary ⟨x.val, boundary⟩]
    exact (B.boundaryDirection ⟨x.val, boundary⟩).property

end Unfoldings.RadialBody
