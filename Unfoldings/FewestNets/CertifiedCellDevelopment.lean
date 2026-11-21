module

public import Unfoldings.FewestNets.IcosahedronCertifiedCellRouting
public import Unfoldings.Roof.AdaptiveComponentDevelopment
public import Unfoldings.Roof.ClippedPhysicalCurvature

/-! A checked finite routing record produces an original-edge net for each selected component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open Real InnerProductGeometry MeshStar

universe u v

private theorem normal_height_of_slope_radius {φ : ℝ} (pos : 0 < φ) (small : φ < π / 2)
    (h : ℝ) (s : Plane) (radius : ‖s‖ ≤ tan φ) : cos φ ≤ (SpatialPlane.ofGraph h s).normal 2 := by
  have cp : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [pos, pi_pos], small⟩
  have sq := pow_le_pow_left₀ (norm_nonneg _) radius 2
  have tc : tan φ * cos φ = sin φ := by
    rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ cp.ne']
  have exact_sq : tan φ ^ 2 * cos φ ^ 2 = sin φ ^ 2 := by
    rw [← mul_pow, tc]
  apply graphNormal_vertical_ge cp.le
  have mul := mul_le_mul_of_nonneg_right sq (sq_nonneg (cos φ))
  nlinarith only [mul, exact_sq, sin_sq_add_cos_sq φ]

private theorem exists_model_of_verified_halfplanes
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
    {S : Set Plane} (compact : IsCompact S) (present : S.Nonempty)
    {n : ℕ} (normal : Fin (n + 1) → Plane) (offset : Fin (n + 1) → ℝ)
    (polygon : ∀ p, p ∈ S ↔ ∀ i, inner ℝ p (normal i) ≤ offset i)
    (strict : ∀ i, 0 < offset i) :
    Nonempty (K.clippedExtension S compact present).FiniteSlopeModel := by
  let line (i : ULift.{u} (Fin (n + 1))) : Plane →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ Plane (offset i.down) - (innerSL ℝ (normal i.down)).toLinearMap.toAffineMap
  have clip : AffineEnvelope.clip line 0 = S := by
    ext p
    rw [polygon]
    constructor
    · intro member i
      have h := member.trans (AffineEnvelope.height_le line p (ULift.up i))
      change 0 ≤ offset i - inner ℝ (normal i) p at h
      exact (real_inner_comm (normal i) p).le.trans (sub_nonneg.mp h)
    · intro member
      obtain ⟨i, equal⟩ := AffineEnvelope.exists_height_eq line p
      change 0 ≤ AffineEnvelope.height line p
      rw [equal]
      change 0 ≤ offset i.down - inner ℝ (normal i.down) p
      exact sub_nonneg.mpr ((real_inner_comm p (normal i.down)).le.trans (member i.down))
  have inside : 0 < AffineEnvelope.height line 0 := by
    obtain ⟨i, at_min⟩ := AffineEnvelope.exists_height_eq line (0 : Plane)
    rw [at_min]
    change 0 < offset i.down - inner ℝ (normal i.down) 0
    simpa only [inner_zero_right, sub_zero] using strict i.down
  subst S
  exact ⟨K.clippedPhysicalModel line compact inside⟩

set_option maxHeartbeats 1400000 in
open Classical in
/-- Verified body and side data, the checked scalar bounds, and the actual
tilt and projected triangle-angle bounds give a net on original seams. -/
theorem hasOriginalEdgeNet_of_checked_witness
    {q n m D : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
    (R : MeshStarRealization a M) (hq : 0 < q) (qbig : 100 ≤ q)
    (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
    (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
    (pred_ne : ∀ k : Fin (n + 1), k ≠ k - 1)
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
    {ρ : ℝ} (positive : 0 < ρ) (hD : 0 < D)
    (cp : ∀ k, CheckedPlane D (ρ⁻¹ • M.physicalVertex k))
    (cn : ∀ k, CheckedPlane D (M.physicalSideNormal k))
    (co : ∀ k, CheckedReal D (M.physicalSideOffset k / ρ))
    (scalar : DevelopmentScalarRecord) (w : RoutingCellWitness (n + 1) (m + 1)) {target : ℚ}
    (target_nonnegative : 0 ≤ target) (valid : scalar.ValidFor target)
    (cot_gap : 0 < scalar.cotangentGap) (interior_gap : 0 < scalar.interiorMarginGap target)
    (passed : w.check hD cp cn co scalar = true)
    (height_bound : (3 : ℝ) / 4 ≤ cos scalar.tilt)
    (gap : 0 < developmentGaps scalar.tilt scalar.margin scalar.lengthConstant 0)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier (convexHull ℝ (Set.range M.physicalVertex)))
    (radius : ∀ x ∈ convexHull ℝ (Set.range M.physicalVertex), ‖x‖ ≤ tan scalar.tilt)
    (angles : ∀ f, K.normalSlope f ∈ convexHull ℝ (Set.range M.physicalVertex) →
      ∀ i, (K.projectedTriangle f).cornerAngle i ≤ scalar.projectedAngle target) :
    ∀ seed, K.normalSlope seed ∈ convexHull ℝ (Set.range M.physicalVertex) →
      C.HasOriginalEdgeNet (K.selectionComponent (convexHull ℝ (Set.range M.physicalVertex)) seed) := by
  let S := convexHull ℝ (Set.range M.physicalVertex)
  let compact : IsCompact S := (Set.finite_range _).isCompact_convexHull ℝ
  let present : S.Nonempty := ⟨M.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
  let normal := M.physicalSideNormal
  have neighbor (k : Fin (n + 1)) := R.bisectorTangent_neighbor_ne_zero hq k
  have unit (k : Fin (n + 1)) : ‖normal k‖ = 1 :=
    M.physicalSideNormal_unit k (R.direction_unit hq) genuine (neighbor k)
  obtain ⟨rpos, disk, _, geo⟩ :=
    w.geometry_of_check hD cp cn co scalar target_nonnegative valid cot_gap passed unit
  have offset_pos (i : Fin (n + 1)) : 0 < M.physicalSideOffset i := by
    have zero : (0 : Plane) ∈ w.progressBody :=
      disk (by simpa only [Metric.mem_closedBall, dist_self] using rpos.le)
    have h := (geo i).1 zero
    change inner ℝ (normal i) 0 < M.physicalSideOffset i / ρ at h
    rw [inner_zero_right] at h
    simpa only [zero_mul] using (lt_div_iff₀ positive).mp h
  obtain ⟨F⟩ := exists_model_of_verified_halfplanes K compact present normal
    M.physicalSideOffset (R.mem_physicalPolygon_iff_side_le qbig hq outward genuine neighbor)
    offset_pos
  let L := (fun x : Plane => ρ • x) '' w.progressBody
  let r := ρ * (w.inradius : ℝ)
  let b := (scalar.lengthConstant : ℝ) * r
  have rpos' : 0 < r := mul_pos positive rpos
  have bpos : 0 < b := mul_pos (by exact_mod_cast valid.2.2.2.2.2.2.2) rpos'
  have disk' : Metric.closedBall (0 : Plane) r ⊆ L := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have scaled : ρ⁻¹ • x ∈ w.progressBody := by
      apply disk
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr positive), ← div_eq_inv_mul, div_le_iff₀ positive]
      exact hx.trans_eq (mul_comm _ _)
    refine ⟨ρ⁻¹ • x, scaled, ?_⟩
    change ρ • (ρ⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ positive.ne', one_smul]
  obtain ⟨boundary, ⟨routing⟩, upper⟩ := R.exists_compatibleAdaptiveRouting_of_checked_witness
    hq qbig outward genuine pred_ne K positive hD cp cn co scalar w target_nonnegative valid
    cot_gap interior_gap passed no_boundary angles
  have choose : r • normal 0 ∈ Metric.closedBall (0 : Plane) r := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos rpos',
      unit 0, mul_one]
  have ratio : r ≤ b := by
    have h := upper _ (routing.within (disk' choose))
    change ‖r • normal 0‖ < b at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos rpos', unit 0, mul_one] at h
    exact h.le
  have φpos : (0 : ℝ) < scalar.tilt := by exact_mod_cast valid.1
  have φlt : (scalar.tilt : ℝ) < 1 := by exact_mod_cast valid.2.1
  have φsmall : (scalar.tilt : ℝ) < π / 2 := by linarith only [φlt, pi_gt_three]
  have tilt (i : F.Face) : cos scalar.tilt ≤ (F.plane i).normal 2 :=
    normal_height_of_slope_radius φpos φsmall _ _ (radius _ (F.included i.val i.property))
  have γpos : (0 : ℝ) < scalar.margin := by exact_mod_cast valid.2.2.2.2.2.1
  have radial : (scalar.margin : ℝ) ≤
      cos ((π - scalar.visualAngle + scalar.projectedAngle target) / 2) := by
    rw [scalar.interiorMarginGap_eq] at interior_gap
    exact (sub_pos.mp interior_gap).le
  have length : b / r ≤ scalar.lengthConstant := by
    change (scalar.lengthConstant : ℝ) * r / r ≤ _
    rw [mul_div_cancel_right₀ _ rpos'.ne']
  have small := sub_pos.mp (show 0 < (scalar.margin : ℝ) -
    radialBlockError (cos scalar.tilt)⁻¹ (shallowDevelopmentHeading scalar.tilt) scalar.lengthConstant
      (sqrt (1 - (scalar.margin : ℝ) ^ 2)) π from gap)
  exact K.hasOriginalEdgeNet_of_adaptiveRouting (convex_convexHull ℝ _) compact present routing
    no_boundary F rpos' disk' bpos ratio (fun x hx => (upper x hx).le) φpos φsmall height_bound tilt
    γpos (scalar.margin_lt_one valid).le radial le_rfl length small

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
