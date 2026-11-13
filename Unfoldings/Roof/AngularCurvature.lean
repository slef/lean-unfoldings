module

public import Unfoldings.Cap.AngularCurvature

public import Unfoldings.Roof.LinkCrossings
public import Unfoldings.Roof.Boundary

/-!
# Intrinsic vertex curvature is actual outward solid angle

The equality is derived from the actual convex link and the crossing integral.
Flat vertices and degenerate normal polygons require no separate positive-curvature case.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal

namespace ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The polyhedral Gauss identity follows from genuine geometry, without an assumed area formula. -/
theorem angular_defect_eq_solid_normal (v : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    ENNReal.ofReal (2 * Real.pi - C.totalAngle Set.univ v) =
      solidAngleMeasure (K.sphericalNormalPolygon v) := by
  classical
  obtain ⟨m, c, closes, covers⟩ := C.exists_cyclic_link Set.univ v internal
  have inside := (K.projectedVertex_mem_interior_iff v).mpr internal
  let f : Space →L[ℝ] ℝ := EuclideanSpace.proj 2
  have fne : f ≠ 0 := by
    intro equal
    have evaluated := congrArg (fun g : Space →L[ℝ] ℝ => g (Cap.northLift 0)) equal
    change (1 : ℝ) = 0 at evaluated
    norm_num at evaluated
  have away : ∀ᵐ n ∂solidAngleMeasure, ∀ p : C.LinkGerm Set.univ v,
      inner ℝ n (K.folding.germDirection p.val) ≠ 0 :=
    ae_all_iff.mpr (fun p => ae_inner_ne_zero (K.folding.germDirection_ne_zero p.val))
  have sphere : ∀ᵐ n ∂solidAngleMeasure, n ∈ Metric.sphere (0 : Space) 1 := by
    rw [ae_iff]
    exact solidAngleMeasure_off_sphere
  have crossings : ∀ᵐ n ∂solidAngleMeasure.restrict {n | 0 < f n},
      angularCrossings (fun i => K.folding.germDirection (c.point i).val) (finRotate (m + 1)) n =
        ({n | 0 < f n} \ K.sphericalNormalPolygon v).indicator (fun _ => 2) n := by
    filter_upwards [ae_restrict_of_ae away, ae_restrict_of_ae sphere,
      ae_restrict_mem ((isOpen_lt continuous_const f.continuous).measurableSet)]
      with n hn hunit hupper
    have unit : ‖n‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hunit
    rw [K.link_crossings_eq_zero_or_two c closes covers inside n unit hupper hn]
    by_cases present : n ∈ K.sphericalNormalPolygon v <;> simp [present, hupper]
  have identity := angular_defect_eq_solidAngle_of_crossings
    (fun i => K.folding.germDirection (c.point i).val) (finRotate (m + 1))
    (fun i => K.folding.germDirection_ne_zero _) f fne (K.sphericalNormalPolygon v)
    (K.compact_sphericalNormalPolygon v).measurableSet
    (fun n present => (K.sphericalNormalPolygon_unit present).2) crossings
  rwa [K.folding.sum_germDirection_angles c closes covers] at identity

end ConvexRoof
end Unfoldings
