module

public import Unfoldings.Cap.CrossingPotential
public import Unfoldings.Cap.ParentSegments
public import Unfoldings.Geometry.SectionRayCounter

/-!
# Actual parent-edge ray counters along section parameters

The geometric segment counter is exactly the already bounded forest-ray
counter in the positive horizontal section frame. Its weighted sum is therefore
bounded uniformly by total cap curvature at every section query.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

def parentSectionCounter (p q : Plane) (r : ℝ) (e : C.Vertex Set.univ) : ℝ :=
  sectionRayCounter p q (K.projectedVertex e) (K.projectedVertex (M.parents.parent e)) r

/-- The physical parent-segment counter is the actual signed forest-ray counter. -/
theorem parentSectionCounter_eq_ray (p q : Plane) (r : ℝ) (e : C.Vertex Set.univ) :
    M.parentSectionCounter p q r e = M.parentRayCrossingInFrame
      (positiveDirectionFrame (q - p)) p (r * ‖q - p‖) 0 e := by
  let a := positiveDirectionFrame (q - p) (K.projectedVertex e - p)
  let b := positiveDirectionFrame (q - p) (K.projectedVertex (M.parents.parent e) - p)
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
  ∑ e : C.Vertex Set.univ, if e ∉ M.parents.roots then
    M.parentSectionCounter p q r e * M.subtreeCurvature e else 0

theorem sectionCurvaturePotential_eq_ray (p q : Plane) (r : ℝ) :
    M.sectionCurvaturePotential p q r = M.rayCurvaturePotential
      (positiveDirectionFrame (q - p)) p (r * ‖q - p‖) 0 := by
  simp only [sectionCurvaturePotential, rayCurvaturePotential, M.parentSectionCounter_eq_ray]

theorem abs_sectionCurvaturePotential_le (positive : 0 < t) (small : t < 1)
    (p q : Plane) (r : ℝ) :
    |M.sectionCurvaturePotential p q r| ≤ C.totalInteriorAngularDefect Set.univ := by
  rw [M.sectionCurvaturePotential_eq_ray]
  exact M.abs_rayCurvaturePotential_le positive small _ _ _ _

open scoped Classical in
/-- Potential differences sum the actual signed changes of the actual original parent counters. -/
theorem sectionCurvaturePotential_sub (p q : Plane) (first last : ℝ) :
    M.sectionCurvaturePotential p q last - M.sectionCurvaturePotential p q first =
      ∑ e : C.Vertex Set.univ, if e ∉ M.parents.roots then
        (M.parentSectionCounter p q last e - M.parentSectionCounter p q first e) *
          M.subtreeCurvature e else 0 := by
  simp only [sectionCurvaturePotential]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases nonroot : e ∉ M.parents.roots
  · simp only [ite_eq_left nonroot]
    ring
  · simp only [ite_eq_right nonroot, sub_self]

end Unfoldings.ConvexCap.SectorForest
