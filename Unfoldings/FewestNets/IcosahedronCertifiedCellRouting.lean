module

public import Unfoldings.FewestNets.CheckedRoutingCell
public import Unfoldings.FewestNets.IcosahedronRotatedUpperRoof
public import Unfoldings.Roof.ScaledAdaptiveRouting

/-! Any checked mesh-cell record gives the physical adaptive forest and length ratio. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron.MeshStarRealization

open InnerProductGeometry Real MeshStar Topology

universe u v

variable {q n m D : ℕ} {a : meshSites q} {M : MeshStar (n + 1)}
  (R : MeshStarRealization a M) (hq : 0 < q) (qbig : 100 ≤ q)
  (outward : ∀ k, 0 < inner ℝ M.direction (M.dual k))
  (genuine : bisectorTangent M.direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0)
  (pred_ne : ∀ k : Fin (n + 1), k ≠ k - 1)

include R hq qbig outward genuine pred_ne in
open Classical in
/-- Use the finite side witnesses of a realized cell to construct adaptive
parents in its literal physical slope polygon. The row's length ratio
scales with the inradius and has the same value in both coordinates. -/
theorem exists_compatibleAdaptiveRouting_of_checked_witness
    {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
    {ρ : ℝ} (positive : 0 < ρ) (hD : 0 < D)
    (cp : ∀ k, CheckedPlane D (ρ⁻¹ • M.physicalVertex k))
    (cn : ∀ k, CheckedPlane D (M.physicalSideNormal k))
    (co : ∀ k, CheckedReal D (M.physicalSideOffset k / ρ))
    (scalar : DevelopmentScalarRecord) (w : RoutingCellWitness (n + 1) (m + 1)) {target : ℚ}
    (target_nonnegative : 0 ≤ target) (valid : scalar.ValidFor target)
    (cot_gap : 0 < scalar.cotangentGap) (interior_gap : 0 < scalar.interiorMarginGap target)
    (passed : w.check hD cp cn co scalar = true)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier (convexHull ℝ (Set.range M.physicalVertex)))
    (angles : ∀ f, K.normalSlope f ∈ convexHull ℝ (Set.range M.physicalVertex) →
      ∀ i, (K.projectedTriangle f).cornerAngle i ≤ scalar.projectedAngle target) :
    let slopes := convexHull ℝ (Set.range M.physicalVertex)
    let compact : IsCompact slopes := (Set.finite_range _).isCompact_convexHull ℝ
    let present : slopes.Nonempty := ⟨M.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
    ∃ boundary : (frontier slopes).Nonempty,
      Nonempty (K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
        (K.clippedExtension slopes compact present) boundary
        ((fun x : Plane => ρ • x) '' w.progressBody) (ρ * w.inradius)
        (cos ((π - scalar.visualAngle + scalar.projectedAngle target) / 2)) scalar.margin) ∧
      ∀ x ∈ slopes, ‖x‖ < (scalar.lengthConstant : ℝ) * (ρ * w.inradius) := by
  let slopes := convexHull ℝ (Set.range M.physicalVertex)
  let L := w.progressBody
  let normal := M.physicalSideNormal
  let side (k : Fin (n + 1)) := R.bisectorTangent_neighbor_ne_zero hq k
  have unit (k : Fin (n + 1)) : ‖normal k‖ = 1 :=
    M.physicalSideNormal_unit k (R.direction_unit hq) genuine (side k)
  obtain ⟨rpos, disk, radius, geometry⟩ := w.geometry_of_check hD cp cn co scalar
    target_nonnegative valid cot_gap passed unit
  have halfplanes := R.mem_physicalPolygon_iff_side_le qbig hq outward genuine side
  have compact : IsCompact slopes := (Set.finite_range _).isCompact_convexHull ℝ
  have present : slopes.Nonempty :=
    ⟨M.physicalVertex 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
  have proper : slopes ≠ Set.univ := by
    intro all
    let offset := M.physicalSideOffset 0
    have member : (offset + 1) • normal 0 ∈ slopes := by rw [all]; trivial
    have h := (halfplanes _).mp member 0
    change inner ℝ ((offset + 1) • normal 0) (normal 0) ≤ offset at h
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, unit 0] at h
    linarith
  have boundary : (frontier slopes).Nonempty := nonempty_frontier_iff.mpr ⟨present, proper⟩
  have image_eq : (fun x : Plane => ρ⁻¹ • x) '' slopes =
      convexHull ℝ (Set.range (fun k => ρ⁻¹ • M.physicalVertex k)) := by
    let scale : Plane →ₗ[ℝ] Plane := ρ⁻¹ • LinearMap.id
    change scale '' convexHull ℝ (Set.range M.physicalVertex) = _
    rw [scale.image_convexHull, ← Set.range_comp]
    rfl
  have contained : L ⊆ (fun x : Plane => ρ⁻¹ • x) '' slopes := by
    intro x hx
    refine ⟨ρ • x, (halfplanes _).mpr ?_, ?_⟩
    · intro k
      have h := (geometry k).1 hx
      change inner ℝ (normal k) x < M.physicalSideOffset k / ρ at h
      change inner ℝ (ρ • x) (normal k) ≤ M.physicalSideOffset k
      rw [real_inner_smul_left, real_inner_comm (normal k) x, mul_comm]
      exact ((lt_div_iff₀ positive).mp h).le
    · change ρ⁻¹ • (ρ • x) = x
      rw [smul_smul, inv_mul_cancel₀ positive.ne', one_smul]
  refine ⟨boundary, ?_, ?_⟩
  · have aperture := scalar.projectedAngle_lt_visualAngle_of_gap target_nonnegative valid interior_gap
    apply K.exists_compatibleAdaptiveRouting_of_scaled_rim (convex_convexHull ℝ _) compact present
      boundary no_boundary positive L contained rpos disk
      (scalar.projectedAngle_nonneg target_nonnegative) (by linarith only [aperture]) angles
    intro p hp
    rw [image_eq] at hp
    have at_side := R.frontier_normalizedPolygon_subset_sides qbig hq outward genuine side
      pred_ne positive.ne' hp
    obtain ⟨k, on_segment⟩ := Set.mem_iUnion.mp at_side
    obtain ⟨t, ht, exact_point⟩ := (segment_eq_image_lineMap ℝ _ _).le on_segment
    have offset_eq : inner ℝ (normal k) p = M.physicalSideOffset k / ρ := by
      rw [← exact_point]
      exact (real_inner_comm _ _).trans
        (M.normalizedSide_on_support_line (R.direction_unit hq) genuine k
          (R.neighborDirection_unit hq k) (side k) outward ρ t)
    have origin : (0 : Plane) ∈ L := disk (by simpa only [Metric.mem_closedBall, dist_self] using rpos.le)
    have offset_pos : 0 < M.physicalSideOffset k / ρ := by
      simpa only [Set.mem_ofPred_eq, inner_zero_right] using (geometry k).1 origin
    have ⟨cones, polar⟩ := (geometry k).2 t ht (by
      change M.physicalSideOffset k / ρ ≤ inner ℝ (normal k)
        (AffineMap.lineMap (ρ⁻¹ • M.physicalVertex (k - 1)) (ρ⁻¹ • M.physicalVertex k) t)
      rw [exact_point, offset_eq])
    rw [exact_point] at cones polar
    refine ⟨normal k, unit k, by rw [offset_eq]; exact offset_pos, ?_, ?_, ?_⟩
    · rintro _ ⟨x, member, rfl⟩
      have h := (halfplanes x).mp member k
      change inner ℝ (normal k) (ρ⁻¹ • x) ≤ inner ℝ (normal k) p
      rw [real_inner_smul_right, offset_eq, ← div_eq_inv_mul, real_inner_comm x (normal k)]
      exact div_le_div_of_nonneg_right h positive.le
    · obtain ⟨axis, width, nonzero, lower, upper, eq⟩ := cones
      exact ⟨axis, width, nonzero, (aperture.trans lower).le, upper.le, eq⟩
    · intro z hz
      exact (polar z hz).trans_eq (real_inner_comm z (normal k))
  · intro x member
    have normalized : ρ⁻¹ • x ∈ convexHull ℝ (Set.range (fun k => ρ⁻¹ • M.physicalVertex k)) := by
      rw [← image_eq]
      exact ⟨x, member, rfl⟩
    have h := radius _ normalized
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive), ← div_eq_inv_mul,
      div_lt_iff₀ positive] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end Unfoldings.FewestNets.Icosahedron.MeshStarRealization
