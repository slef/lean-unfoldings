module

public import Unfoldings.Cap.CompletedCrossingPotential
public import Unfoldings.Cap.CompletedRootPathSupport
public import Unfoldings.Geometry.SectionRayCounter

/-! Actual section counters and curvature potentials for completed roof forests. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (R : K.RadialCutForest source cuts)

theorem parent_segment_eq_original_seam
    (e : {w : C.Vertex Set.univ // w ∉ R.spanningCompletion.parents.roots}) :
    segment ℝ (K.projectedVertex e.val)
      (K.projectedVertex (R.spanningCompletion.parents.parent e.val)) =
        (K.projectedTriangle (C.left (R.spanningCompletion.selection.edge e)).face).edge
          (C.left (R.spanningCompletion.selection.edge e)).edge :=
  K.selected_parent_segment_eq_seam R.spanningCompletion.selection e

def parentSectionCounter (p q : Plane) (r : ℝ) (e : C.Vertex Set.univ) : ℝ :=
  sectionRayCounter p q (K.projectedVertex e) (K.projectedVertex
    (R.spanningCompletion.parents.parent e)) r

/-- The physical parent-segment counter is the actual signed forest-ray counter. -/
theorem parentSectionCounter_eq_ray (p q : Plane) (r : ℝ) (e : C.Vertex Set.univ) :
    R.parentSectionCounter p q r e = R.completedParentRayCrossing
      (positiveDirectionFrame (q - p)) p (r * ‖q - p‖) 0 e := by
  let a := positiveDirectionFrame (q - p) (K.projectedVertex e - p)
  let b := positiveDirectionFrame (q - p) (K.projectedVertex (R.spanningCompletion.parents.parent
    e) - p)
  have point (s : ℝ) : AffineMap.lineMap a b s 0 = (1 - s) * a 0 + s * b 0 := by
    simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]
    ring
  change (if r * ‖q - p‖ < AffineMap.lineMap a b (levelCrossingParameter (a 1) (b 1) 0) 0
    then levelIndicator 0 (b 1) - levelIndicator 0 (a 1) else 0) = _
  rw [point]
  rfl

open scoped Classical in
def sectionCurvaturePotential (p q : Plane) (r : ℝ) : ℝ :=
  ∑ e : C.Vertex Set.univ, if e ∉ R.spanningCompletion.parents.roots then
    R.parentSectionCounter p q r e * R.completedSubtreeCurvature e else 0

theorem sectionCurvaturePotential_eq_ray (p q : Plane) (r : ℝ) :
    R.sectionCurvaturePotential p q r = R.completedRayCurvaturePotential
      (positiveDirectionFrame (q - p)) p (r * ‖q - p‖) 0 := by
  simp only [sectionCurvaturePotential, completedRayCurvaturePotential,
    R.parentSectionCounter_eq_ray]

theorem abs_sectionCurvaturePotential_le (wedges : R.CurvedPathWedges)
    (p q : Plane) (r : ℝ) :
    |R.sectionCurvaturePotential p q r| ≤ C.totalInteriorAngularDefect Set.univ := by
  rw [R.sectionCurvaturePotential_eq_ray]
  exact R.abs_completedRayCurvaturePotential_le wedges _ _ _ _

open scoped Classical in
/-- Potential differences sum the actual signed changes of the actual original parent counters. -/
theorem sectionCurvaturePotential_sub (p q : Plane) (first last : ℝ) :
    R.sectionCurvaturePotential p q last - R.sectionCurvaturePotential p q first =
      ∑ e : C.Vertex Set.univ, if e ∉ R.spanningCompletion.parents.roots then
        (R.parentSectionCounter p q last e - R.parentSectionCounter p q first e) *
          R.completedSubtreeCurvature e else 0 := by
  simp only [sectionCurvaturePotential]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases nonroot : e ∉ R.spanningCompletion.parents.roots
  · simp only [ite_eq_left nonroot]
    ring
  · simp only [ite_eq_right nonroot, sub_self]

end Unfoldings.ConvexCap.RadialCutForest
