module

public import Unfoldings.Roof.GradientSelection

public import Unfoldings.Roof.SupportingEnvelope
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Geometry.SupportingSlopes
public import Mathlib.Tactic.GCongr

/-!
# Planar normal images of convex roof vertices

Use gnomonic slopes `normal.xy / normal.z`. The convex hull of incident slopes
supports the actual cap roof, so normal polygons of distinct vertices have
disjoint interiors. All polygons lie in one disk controlled by the maximum
normal tilt. Relating their area to intrinsic curvature is a further theorem.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem supportHeight_difference (f : Face) (p q : Plane) :
    K.supportHeight f q = K.supportHeight f p - inner ℝ (K.normalSlope f) (q - p) := by
  simp only [supportHeight_apply, normalSlope, real_inner_smul_left, inner_sub_right]
  ring

theorem normalSlope_supports {f : Face} {p : Plane}
    (contact : K.supportHeight f p = K.roofHeight p) :
    K.normalSlope f ∈ supportingSlopes K.roofHeight p := by
  intro q
  calc
    K.roofHeight q ≤ K.supportHeight f q := K.roofHeight_le_supportHeight q f
    _ = K.roofHeight p - inner ℝ (K.normalSlope f) (q - p) := by
      rw [K.supportHeight_difference f p q, contact]

def incidentSlopes (v : C.Vertex Set.univ) : Set Plane :=
  {g | ∃ f i, C.vertexOfCorner Set.univ (f, i) = v ∧ K.normalSlope f = g}

def normalPolygon (v : C.Vertex Set.univ) : Set Plane := convexHull ℝ (K.incidentSlopes v)

theorem finite_incidentSlopes (v : C.Vertex Set.univ) : (K.incidentSlopes v).Finite :=
  (Set.finite_range K.normalSlope).subset (by rintro _ ⟨f, _, _, rfl⟩; exact ⟨f, rfl⟩)

theorem compact_normalPolygon (v : C.Vertex Set.univ) : IsCompact (K.normalPolygon v) :=
  (K.finite_incidentSlopes v).isCompact_convexHull ℝ

theorem normalPolygon_supports (v : C.Vertex Set.univ) :
    K.normalPolygon v ⊆ supportingSlopes K.roofHeight (K.projectedVertex v) := by
  apply convexHull_min ?_ (convex_supportingSlopes K.roofHeight (K.projectedVertex v))
  rintro _ ⟨f, i, vertex, rfl⟩
  apply K.normalSlope_supports
  rw [← vertex, K.projectedVertex_ofCorner]
  exact (K.supportHeight_face f ((C.triangle f).vertex i)).trans
    (K.roofHeight_face f ⟨(C.triangle f).vertex i, (C.triangle f).vertex_mem i⟩).symm

/-- Distinct actual vertices have normal polygons with disjoint interiors. -/
theorem normalPolygons_nonoverlapping {v w : C.Vertex Set.univ} (different : v ≠ w) :
    Disjoint (interior (K.normalPolygon v)) (interior (K.normalPolygon w)) := by
  have disjoint := supportingSlopes_interiors_disjoint K.roofHeight
    (K.projectedVertex_injective.ne different)
  apply Set.disjoint_left.mpr
  intro g first last
  exact Set.disjoint_left.mp disjoint
    (interior_mono (K.normalPolygon_supports v) first)
    (interior_mono (K.normalPolygon_supports w) last)

/-- The gnomonic normal disk shrinks to zero with the maximum normal tilt. -/
theorem normalSlope_norm_le {c : ℝ} (positive : 0 < c) (height : ∀ f, c ≤ K.normal f 2)
    (f : Face) : ‖K.normalSlope f‖ ≤ Real.sqrt (1 - c ^ 2) / c := by
  have split := Cap.horizontal_norm_sq (K.normal f)
  rw [K.normal_unit] at split
  have squared := mul_self_le_mul_self positive.le (height f)
  have nonnegative : 0 ≤ 1 - c ^ 2 := by nlinarith [sq_nonneg ‖Cap.horizontal (K.normal f)‖]
  have root := Real.sq_sqrt nonnegative
  have bound : ‖Cap.horizontal (K.normal f)‖ ≤ Real.sqrt (1 - c ^ 2) := by
    nlinarith [norm_nonneg (Cap.horizontal (K.normal f)), Real.sqrt_nonneg (1 - c ^ 2)]
  rw [normalSlope, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (K.normal_upward f)),
    mul_comm, ← div_eq_mul_inv]
  gcongr
  exact height f

theorem normalPolygon_subset_disk {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) (v : C.Vertex Set.univ) :
    K.normalPolygon v ⊆ Metric.closedBall (0 : Plane) (Real.sqrt (1 - c ^ 2) / c) := by
  apply convexHull_min ?_ (convex_closedBall _ _)
  rintro _ ⟨f, _, _, rfl⟩
  apply Metric.mem_closedBall.mpr
  simpa only [dist_zero_right] using K.normalSlope_norm_le positive height f

end Unfoldings.ConvexRoof
