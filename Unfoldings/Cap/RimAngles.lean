module

public import Unfoldings.Cap.BoundaryGerms
public import Unfoldings.Cap.ProjectedInterval
public import Unfoldings.Cap.UniformCurvature

/-! Pointwise nonnegative rim angle excess and bounds for arbitrary rim portions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

theorem horizontal_angle_of_height_zero {x y : Space} (hx : x 2 = 0) (hy : y 2 = 0) :
    InnerProductGeometry.angle (horizontal x) (horizontal y) = InnerProductGeometry.angle x y := by
  have restore (z : Space) (height : z 2 = 0) : horizontalLiftIsometry (horizontal z) = z := by
    apply dist_eq_zero.mp
    rw [dist_comm]
    change dist z (horizontalLift (horizontal z)) = 0
    rw [dist_horizontalLift_horizontal, height, abs_zero]
  have identity := horizontalLiftIsometry.angle_map (horizontal x) (horizontal y)
  rw [restore x hx, restore y hy] at identity
  exact identity.symm

end Unfoldings.Cap

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {v : C.Vertex Set.univ}

theorem germFarPoint_projection_mem_footprint (p : C.Germ) :
    Cap.horizontal (K.folding.germFarPoint p) ∈ K.footprint := by
  refine ⟨K.folding.germFarPoint p, Set.mem_iUnion.mpr ⟨p.1.1, ?_⟩, rfl⟩
  exact ⟨(C.triangle p.1.1).vertex (C.germFarCorner p).2,
    (C.triangle p.1.1).vertex_mem _, rfl⟩

/-- The first boundary bank supports all incident directions on the same weak side. -/
theorem boundary_germ_same_side (p : C.LinkGerm Set.univ v)
    (boundary : C.IsBoundaryEdge Set.univ (C.germEdge p.val))
    (r s : C.LinkGerm Set.univ v) :
    0 ≤ orient 0 (K.projectedGermRay p) (K.projectedGermRay r) *
      orient 0 (K.projectedGermRay p) (K.projectedGermRay s) := by
  let far (a : C.LinkGerm Set.univ v) := Cap.horizontal (K.folding.germFarPoint a.val)
  have identity (a : C.LinkGerm Set.univ v) :
      orient 0 (K.projectedGermRay p) (K.projectedGermRay a) =
        orient (K.projectedVertex v) (far p) (far a) := by
    simp only [projectedGermRay, orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero, far]
  rw [identity, identity]
  obtain ⟨x, inside⟩ := K.interior_projection
  have different : K.projectedVertex v ≠ far p :=
    (sub_ne_zero.mp (K.projectedGermRay_ne_zero p)).symm
  have edge := K.boundary_germ_segment_frontier p boundary
  have nonzero := orient_ne_zero_of_boundary_segment K.convex_projection
    K.compact_footprint.isClosed inside different edge
  have first := orient_mul_nonneg_of_boundary_segment K.convex_projection
    K.compact_footprint.isClosed inside different edge
    (K.germFarPoint_projection_mem_footprint r.val)
  have second := orient_mul_nonneg_of_boundary_segment K.convex_projection
    K.compact_footprint.isClosed inside different edge
    (K.germFarPoint_projection_mem_footprint s.val)
  have product : 0 ≤ (orient (K.projectedVertex v) (far p) (far r) *
      orient (K.projectedVertex v) (far p) (far s)) *
        (orient (K.projectedVertex v) (far p) x) ^ 2 := by
    convert mul_nonneg first second using 1; ring
  have square := sq_pos_of_ne_zero nonzero
  by_contra negative
  exact (not_lt_of_ge product) (mul_neg_of_neg_of_pos (lt_of_not_ge negative) square)

variable {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

/-- A convex boundary interval fan subtends its exact endpoint angle, including straight corners. -/
theorem projected_boundary_angle_eq_endpoint
    (start : C.linkMate Set.univ v c.first = c.first) (covers : ∀ p, c.Visited p) :
    K.projectedTotalAngle Set.univ v =
      InnerProductGeometry.angle (K.projectedGermRay c.first)
        (K.projectedGermRay (C.linkTurn Set.univ v c.last)) := by
  have boundary := (C.linkMate_eq_self_iff Set.univ v c.first).mp start
  have first : K.projectedIntervalRay c 0 = K.projectedGermRay c.first := by
    change K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    rfl
  have halfplane (i : Fin (n + 2)) :
      0 ≤ orient 0 (K.projectedIntervalRay c 0) (K.projectedIntervalRay c i) *
        orient 0 (K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc)
          (K.projectedIntervalRay c (0 : Fin (n + 1)).succ) := by
    have represented : ∃ p : C.LinkGerm Set.univ v,
        K.projectedIntervalRay c i = K.projectedGermRay p := by
      refine Fin.lastCases ?_ (fun k => ?_) i
      · exact ⟨C.linkTurn Set.univ v c.last, K.projectedIntervalRay_last c⟩
      · exact ⟨c.point k, K.projectedIntervalRay_castSucc c k⟩
    obtain ⟨p, equal⟩ := represented
    rw [equal, first, K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
    exact K.boundary_germ_same_side c.first boundary p (C.linkTurn Set.univ v c.first)
  have identity := sum_ray_angles_eq_endpoint (K.projectedIntervalRay c)
    (K.projectedIntervalRay_ne_zero c)
    (fun i => by
      rw [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ]
      exact K.projectedGermRay_orient_ne_zero (c.point i))
    (K.projectedInterval_orient_sign c covers) halfplane
  rwa [K.sum_projectedInterval_angles c covers, first, K.projectedIntervalRay_last] at identity

/-- Every original convex rim angle increases weakly when lifted to the cap. -/
theorem projected_boundary_angle_le_totalAngle (v : C.Vertex Set.univ)
    (boundary : C.IsBoundaryVertex Set.univ v) :
    K.projectedTotalAngle Set.univ v ≤ C.totalAngle Set.univ v := by
  obtain ⟨n, c, start, finish, covers⟩ := C.exists_interval_link Set.univ v boundary
  rw [K.projected_boundary_angle_eq_endpoint c start covers,
    ← K.horizontal_germDirection, ← K.horizontal_germDirection,
    Cap.horizontal_angle_of_height_zero
      (K.boundary_germDirection_height c.first.val
        ((C.linkMate_eq_self_iff Set.univ v c.first).mp start))
      (K.boundary_germDirection_height (C.linkTurn Set.univ v c.last).val
        ((C.linkMate_eq_self_iff Set.univ v (C.linkTurn Set.univ v c.last)).mp finish))]
  exact K.folding.intervalLink_endpoint_angle_le c covers

/-- The original rim's angle excess; all other vertices contribute zero. -/
def boundaryAngleExcess (v : C.Vertex Set.univ) : ℝ := by
  classical
  exact if C.IsBoundaryVertex Set.univ v then
    C.totalAngle Set.univ v - K.projectedTotalAngle Set.univ v else 0

theorem boundaryAngleExcess_nonneg (v : C.Vertex Set.univ) : 0 ≤ K.boundaryAngleExcess v := by
  classical
  by_cases boundary : C.IsBoundaryVertex Set.univ v
  · simpa only [boundaryAngleExcess, ite_eq_left boundary] using
      sub_nonneg.mpr (K.projected_boundary_angle_le_totalAngle v boundary)
  · simp only [boundaryAngleExcess, ite_eq_right boundary, le_refl]

/-- Relative angle balance now identifies a sum of pointwise nonnegative rim contributions. -/
theorem sum_boundaryAngleExcess :
    (∑ v : C.Vertex Set.univ, K.boundaryAngleExcess v) =
      C.totalInteriorAngularDefect Set.univ := by
  classical
  simpa only [boundaryAngleExcess, TriangleComplex.totalInteriorAngularDefect,
    TriangleComplex.interiorAngularDefect, ite_not] using K.curvature_eq_actual_boundary_excess.symm

/-- Every finite portion of the rim is bounded by total curvature, independently of its size. -/
theorem sum_boundaryAngleExcess_le_totalCurvature (s : Finset (C.Vertex Set.univ)) :
    (∑ v ∈ s, K.boundaryAngleExcess v) ≤ C.totalInteriorAngularDefect Set.univ := by
  rw [← K.sum_boundaryAngleExcess]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun v _ _ => K.boundaryAngleExcess_nonneg v)

include K in
/-- Interior curvature of any selected finite subregion is bounded by the full cap budget. -/
theorem sum_interiorAngularDefect_le_totalCurvature (s : Finset (C.Vertex Set.univ)) :
    (∑ v ∈ s, C.interiorAngularDefect Set.univ v) ≤ C.totalInteriorAngularDefect Set.univ := by
  unfold TriangleComplex.totalInteriorAngularDefect
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun v _ _ => K.interiorCurvature_nonneg v)

/-- One numerical threshold controls every rim portion of every triangulated cap. -/
theorem exists_uniform_tilt_rimExcess_lt {ε : ℝ} (positive : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), K.TiltBound φ → ∀ s : Finset (C'.Vertex Set.univ),
          (∑ v ∈ s, K.boundaryAngleExcess v) < ε := by
  obtain ⟨φ, bounds, budget⟩ := exists_uniform_tilt_totalCurvature_lt positive
  exact ⟨φ, bounds, fun K tilt s =>
    (K.sum_boundaryAngleExcess_le_totalCurvature s).trans_lt (budget K tilt)⟩

end Unfoldings.ConvexCap
