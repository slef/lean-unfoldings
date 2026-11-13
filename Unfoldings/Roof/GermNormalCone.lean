module

public import Unfoldings.Roof.NormalCone

public import Unfoldings.Roof.IncidentDirections

/-! Detecting actual normal-cone membership from all incident edge directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {v : C.Vertex Set.univ}

/-- A local edge test suffices for the actual slope normal polygon. -/
theorem mem_normalPolygon_of_germs_nonpos
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (n : Space) (upward : 0 < n 2)
    (nonpos : ∀ p : C.LinkGerm Set.univ v, inner ℝ n (K.folding.germDirection p.val) ≤ 0) :
    (n 2)⁻¹ • Cap.horizontal n ∈ K.normalPolygon v := by
  by_contra outside
  obtain ⟨functional, c, below, above⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (K.incidentSlopes v)) (K.compact_normalPolygon v).isClosed outside
  let q : Plane := (InnerProductSpace.toDual ℝ Plane).symm functional
  have pairing (z : Plane) : inner ℝ z q = functional z := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have strict (a : C.CornerAt Set.univ v) : 0 < K.germUpperForm v n a q := by
    have slope := below _ (subset_convexHull ℝ _
      (show K.normalSlope a.val.1 ∈ K.incidentSlopes v from
        ⟨a.val.1, a.val.2, a.property, rfl⟩))
    have image : functional ((n 2)⁻¹ • Cap.horizontal n) =
        (n 2)⁻¹ * inner ℝ (Cap.horizontal n) q := by rw [map_smul, ← pairing]; rfl
    rw [image] at above
    have scaled := mul_pos upward (show 0 <
      (n 2)⁻¹ * inner ℝ (Cap.horizontal n) q - functional (K.normalSlope a.val.1) by linarith)
    rw [germUpperForm_apply]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ upward.ne', one_mul] at scaled
    simpa only [pairing] using scaled
  obtain ⟨p, t, a, b, ht, ha, hb, expression⟩ :=
    K.exists_incident_direction_combination v inside q
  let corner : C.CornerAt Set.univ v := ⟨p.val.1, p.property⟩
  have own : K.germUpperForm v n corner (K.projectedGermRay p) =
      inner ℝ n (K.folding.germDirection p.val) := K.germUpperForm_own n p
  have turn := K.germUpperForm_own n (C.linkTurn Set.univ v p)
  change K.germUpperForm v n corner (K.projectedGermRay (C.linkTurn Set.univ v p)) = _ at turn
  have image := congrArg (K.germUpperForm v n corner) expression
  rw [map_smul, map_add, map_smul, map_smul, own, turn] at image
  simp only [smul_eq_mul] at image
  have lhs := mul_pos ht (strict corner)
  have rhs := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (nonpos p))
    (mul_nonpos_of_nonneg_of_nonpos hb (nonpos (C.linkTurn Set.univ v p)))
  linarith

/-- The outward normal image is detected without strict curvature or distinct normals. -/
theorem mem_sphericalNormalPolygon_iff_germs_nonpos
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (n : Space) (unit : ‖n‖ = 1) (upward : 0 < n 2) :
    n ∈ K.sphericalNormalPolygon v ↔
      ∀ p : C.LinkGerm Set.univ v, inner ℝ n (K.folding.germDirection p.val) ≤ 0 := by
  constructor
  · intro present p
    have support := K.sphericalNormalPolygon_supports present (C.germFarCorner p.val).1
      ⟨(C.triangle (C.germFarCorner p.val).1).vertex (C.germFarCorner p.val).2,
        (C.triangle _).vertex_mem _⟩
    rw [← K.folding.linkGerm_apex Set.univ v p] at support
    exact support
  · intro nonpos
    exact ⟨(n 2)⁻¹ • Cap.horizontal n,
      K.mem_normalPolygon_of_germs_nonpos inside n upward nonpos,
      Cap.gnomonicNormal_slope n unit upward⟩

/-- Every genuine upper normal sees a negative edge somewhere around an interior vertex. -/
theorem exists_germ_inner_neg
    (inside : K.projectedVertex v ∈ interior K.footprint)
    (n : Space) (upward : 0 < n 2)
    (nonzero : ∀ p : C.LinkGerm Set.univ v, inner ℝ n (K.folding.germDirection p.val) ≠ 0) :
    ∃ p : C.LinkGerm Set.univ v, inner ℝ n (K.folding.germDirection p.val) < 0 := by
  by_contra none
  push Not at none
  have positive (p : C.LinkGerm Set.univ v) : 0 < inner ℝ n (K.folding.germDirection p.val) :=
    lt_of_le_of_ne (none p) (nonzero p).symm
  obtain ⟨a, original⟩ := C.vertexOfCorner_surjective Set.univ v
  exact K.not_all_projected_germs_positive v inside
    (K.germUpperForm v n ⟨a, original⟩)
    (fun p => (positive p).trans_le (K.germUpperForm_bound n upward _ p))

end Unfoldings.ConvexRoof
