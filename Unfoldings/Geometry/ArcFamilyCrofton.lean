module

public import Unfoldings.Geometry.FiniteArcCrofton
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! Expected crossing multiplicities of finite arc families. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open MeasureTheory InnerProductGeometry
open scoped BigOperators

/-- The number of crossing pairs, with each indexed pair contributing its own crossing. -/
def arcFamilyCrossings {I J : Type*} [Fintype I] [Fintype J]
    (u v : I → Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    (g : SpatialRotation) : ℝ :=
  ∑ i, ∑ j, (arcCrossingEvent (u i) (v i) (frame j) (radius j)).indicator (fun _ => 1) g

theorem integrable_arcCrossingIndicator {u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (nonantipodal : u + v ≠ 0)
    (frame : SpatialRotation) (radius : ℝ) :
    Integrable ((arcCrossingEvent u v frame radius).indicator (fun _ => (1 : ℝ))) probability :=
  (integrable_const 1).indicator₀ (nullMeasurableSet_arcCrossingEvent hu hv nonantipodal frame radius)

theorem integrable_arcFamilyCrossings {I J : Type*} [Fintype I] [Fintype J]
    (u v : I → Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (nonantipodal : ∀ i, u i + v i ≠ 0) :
    Integrable (arcFamilyCrossings u v frame radius) probability :=
  integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_arcCrossingIndicator (hu i) (hv i) (nonantipodal i) (frame j) (radius j)))

/-- Linearity of expectation gives the length product for two whole finite
families. All pairs use the same rotation, so no independence between
different pairs is needed. -/
theorem integral_arcFamilyCrossings {I J : Type*} [Fintype I] [Fintype J]
    (u v : I → Space) (frame : J → SpatialRotation) (radius : J → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (nonantipodal : ∀ i, u i + v i ≠ 0)
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ Real.pi) :
    (∫ g, arcFamilyCrossings u v frame radius g ∂probability) =
      (∑ i, angle (u i) (v i)) * (∑ j, 2 * radius j) / (2 * Real.pi ^ 2) := by
  classical
  let E (i : I) (j : J) := arcCrossingEvent (u i) (v i) (frame j) (radius j)
  have null (i : I) (j : J) : NullMeasurableSet (E i j) probability :=
    nullMeasurableSet_arcCrossingEvent (hu i) (hv i) (nonantipodal i) (frame j) (radius j)
  have integrable (i : I) (j : J) :
      Integrable ((E i j).indicator (fun _ => (1 : ℝ))) probability :=
    integrable_arcCrossingIndicator (hu i) (hv i) (nonantipodal i) (frame j) (radius j)
  have each (i : I) (j : J) :
      (∫ g, (E i j).indicator (fun _ => (1 : ℝ)) g ∂probability) =
        angle (u i) (v i) * (2 * radius j) / (2 * Real.pi ^ 2) := by
    rw [integral_indicator₀ (null i j), setIntegral_const]
    simp only [smul_eq_mul, mul_one, measureReal_def, E, arcCrossingEvent]
    rw [probability_minorArc_rotated_equatorialArc (hu i) (hv i) (nonantipodal i)
      (nonneg j) (small j) (frame j), ENNReal.toReal_ofReal]
    exact div_nonneg (mul_nonneg (angle_nonneg _ _) (by linarith [nonneg j])) (by positivity)
  change (∫ g, ∑ i, ∑ j, (E i j).indicator (fun _ => 1) g ∂probability) = _
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => integrable i j))]
  simp only [integral_finsetSum Finset.univ (fun j _ => integrable _ j), each]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul]

end Unfoldings.SpatialRotation
