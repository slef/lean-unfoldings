module

public import Unfoldings.Geometry.SolidAngleSymmetry
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.ENNReal.BigOperators

/-! Supporting normal cones of a finite spatial convex hull and their total solid angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal BigOperators

variable {I : Type*} (site : I → Space)

/-- The ambient cone of normals maximized at the given hull site. -/
def finiteHullNormalCone (i : I) : Set Space :=
  {n | ∀ j, inner ℝ n (site j) ≤ inner ℝ n (site i)}

theorem mem_finiteHullNormalCone_iff {i : I} {n : Space} :
    n ∈ finiteHullNormalCone site i ↔
      ∀ x ∈ convexHull ℝ (Set.range site), inner ℝ n x ≤ inner ℝ n (site i) := by
  constructor
  · intro hb
    have subset : convexHull ℝ (Set.range site) ⊆ {x | inner ℝ n x ≤ inner ℝ n (site i)} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩
        exact hb j
      · exact convex_halfSpace_le (innerSL ℝ n).toLinearMap.isLinear _
    exact fun _ hx => subset hx
  · intro hb j
    exact hb (site j) (subset_convexHull ℝ _ ⟨j, rfl⟩)

theorem isClosed_finiteHullNormalCone (i : I) : IsClosed (finiteHullNormalCone site i) := by
  have equal :
      finiteHullNormalCone site i = ⋂ j, {n | inner ℝ n (site j) ≤ inner ℝ n (site i)} := by
    ext n
    simp [finiteHullNormalCone]
  rw [equal]
  exact isClosed_iInter (fun j =>
    isClosed_le (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))

theorem iUnion_finiteHullNormalCone [Finite I] [Nonempty I] :
    (⋃ i, finiteHullNormalCone site i) = Set.univ := by
  let := Fintype.ofFinite I
  apply Set.eq_univ_of_forall
  intro n
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset I)
    (fun j => inner ℝ n (site j)) Finset.univ_nonempty
  exact Set.mem_iUnion.mpr ⟨i, fun j => hi j (Finset.mem_univ _)⟩

/-- Distinct hull sites can tie only in a plane of zero solid angle. -/
theorem finiteHullNormalCone_aedisjoint {i j : I} (different : site i ≠ site j) :
    AEDisjoint solidAngleMeasure (finiteHullNormalCone site i) (finiteHullNormalCone site j) := by
  let d := site i - site j
  let f := innerSL ℝ d
  have nonzero : f ≠ 0 := by
    intro zero
    have value := congrArg (fun g : Space →L[ℝ] ℝ => g d) zero
    change inner ℝ d d = 0 at value
    exact different (sub_eq_zero.mp (inner_self_eq_zero.mp value))
  apply le_antisymm _ bot_le
  calc
    _ ≤ solidAngleMeasure {n | f n = 0} := by
      apply measure_mono
      rintro n ⟨hi, hj⟩
      change inner ℝ d n = 0
      rw [real_inner_comm n d, inner_sub_right, sub_eq_zero]
      exact le_antisymm (hj i) (hi j)
    _ = 0 := solidAngleMeasure_ker f nonzero

variable [Fintype I] [Nonempty I]

/-- The actual supporting normal cones, including any zero-area subdivision
sites, have total solid angle (4\pi). -/
theorem sum_solidAngleMeasure_finiteHullNormalCone (injective : Function.Injective site) :
    (∑ i, solidAngleMeasure (finiteHullNormalCone site i)) = ENNReal.ofReal (4 * Real.pi) := by
  have additivity := measure_biUnion_finset₀ (s := (Finset.univ : Finset I))
    (μ := solidAngleMeasure) (f := finiteHullNormalCone site)
    (fun i _ j _ different => finiteHullNormalCone_aedisjoint site (injective.ne different))
    (fun i _ => (isClosed_finiteHullNormalCone site i).measurableSet.nullMeasurableSet)
  simp only [Finset.mem_univ, Set.iUnion_true, iUnion_finiteHullNormalCone,
    solidAngleMeasure_univ] at additivity
  exact additivity.symm

/-- The real area weights used in the component count sum to (4\pi). -/
theorem sum_solidAngle_finiteHullNormalCone (injective : Function.Injective site) :
    (∑ i, (solidAngleMeasure (finiteHullNormalCone site i)).toReal) = 4 * Real.pi := by
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top solidAngleMeasure _),
    sum_solidAngleMeasure_finiteHullNormalCone site injective,
    ENNReal.toReal_ofReal (by positivity)]

end Unfoldings
