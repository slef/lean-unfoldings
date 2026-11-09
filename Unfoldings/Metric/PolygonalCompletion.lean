module

public import Unfoldings.Metric.PolygonalStar
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Completion of the intrinsic metric of a radially accessible planar domain

Proper radial contraction maps every allowed closed-domain step to an allowed
interior step without increasing length. Taking contractions to the identity
proves that including the interior preserves its intrinsic polygonal metric.
For compact domains, the closed domain is complete and this inclusion is dense.
-/

@[expose] public section

open scoped ENNReal Topology
open Filter

noncomputable section

namespace Unfoldings.PolygonalPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (star : StarConvex ℝ (0 : E) s)
  (radial_interior : ∀ x ∈ s, ∀ t : unitInterval, t < 1 → (t : ℝ) • x ∈ interior s)

include star radial_interior

omit star in
theorem starConvex_interior_of_radial_interior : StarConvex ℝ (0 : E) (interior s) := by
  intro x inside a b _ha hb sum
  by_cases full : b = 1
  · simpa only [smul_zero, zero_add, full, one_smul] using inside
  · have before : b < 1 := lt_of_le_of_ne (by linarith) full
    simpa only [smul_zero, zero_add] using
      radial_interior x (interior_subset inside) ⟨b, hb, before.le⟩ before

def shrinkInterior (t : unitInterval) (before : t < 1) (x : PolygonalPoint s) :
    PolygonalPoint (interior s) := ⟨(t : ℝ) • x.val, radial_interior x.val x.property t before⟩

omit star in
theorem shrinkInterior_lipschitz (t : unitInterval) (before : t < 1) :
    LipschitzWith 1 (shrinkInterior radial_interior t before) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  change edist (shrinkInterior radial_interior t before x)
    (shrinkInterior radial_interior t before y) ≤ Route.distance (stepCost (s := s)) x y
  apply Route.le_distance (stepCost (s := s))
    (fun a b => edist (shrinkInterior radial_interior t before a)
      (shrinkInterior radial_interior t before b))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _)
  intro a b
  by_cases inside : segment ℝ a.val b.val ⊆ s
  · rw [stepCost, ite_eq_left inside]
    let A : E →ₗ[ℝ] E := (t : ℝ) • LinearMap.id
    have image : A '' segment ℝ a.val b.val =
        segment ℝ ((t : ℝ) • a.val) ((t : ℝ) • b.val) :=
      image_segment ℝ A.toAffineMap a.val b.val
    have included : segment ℝ ((t : ℝ) • a.val) ((t : ℝ) • b.val) ⊆ interior s := by
      rw [← image]
      rintro _ ⟨w, hw, rfl⟩
      exact radial_interior w (inside hw) t before
    rw [edist_eq_of_segment included, edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    calc
      dist ((t : ℝ) • a.val) ((t : ℝ) • b.val) ≤ ‖(t : ℝ)‖ * dist a.val b.val :=
        dist_smul_le _ _ _
      _ ≤ dist a.val b.val := by
        rw [Real.norm_eq_abs, abs_of_nonneg t.property.1]
        exact mul_le_of_le_one_left dist_nonneg t.property.2
  · simp only [stepCost, ite_eq_right inside, le_top]

omit radial_interior in
theorem tendsto_radialPoint (x : PolygonalPoint s) :
    Tendsto (fun n => radialPoint star (radialApproximation n) x) atTop (𝓝 x) := by
  apply tendsto_iff_edist_tendsto_0.mpr
  have formula (n : ℕ) : edist (radialPoint star (radialApproximation n) x) x =
      ENNReal.ofReal ((1 - (radialApproximation n : ℝ)) * ‖x.val‖) := by
    rw [edist_comm, radial_edist]
  simp only [formula]
  have limit : Tendsto (fun n => (1 - (radialApproximation n : ℝ)) * ‖x.val‖) atTop (𝓝 0) := by
    simpa only [sub_self, zero_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_radialApproximation).mul_const ‖x.val‖
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp limit

omit star in
theorem interior_inclusion_isometry :
    Isometry (inclusion (s := interior s) (t := s) interior_subset) := by
  let star_interior := starConvex_interior_of_radial_interior radial_interior
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using inclusion_lipschitz interior_subset x y
  · have bound (n : ℕ) :
        edist (radialPoint star_interior (radialApproximation n) x)
          (radialPoint star_interior (radialApproximation n) y) ≤
        edist (inclusion interior_subset x) (inclusion interior_subset y) :=
      by simpa only [ENNReal.coe_one, one_mul, radialPoint, shrinkInterior, inclusion] using
        shrinkInterior_lipschitz radial_interior _ (radialApproximation_lt_one n)
          (inclusion interior_subset x) (inclusion interior_subset y)
    exact le_of_tendsto ((tendsto_radialPoint star_interior x).edist
      (tendsto_radialPoint star_interior y)) (Filter.Eventually.of_forall bound)

theorem interior_inclusion_dense :
    DenseRange (inclusion (s := interior s) (t := s) interior_subset) := by
  intro x
  apply mem_closure_of_tendsto (tendsto_radialPoint star x)
  apply Filter.Eventually.of_forall
  intro n
  exact ⟨shrinkInterior radial_interior (radialApproximation n)
    (radialApproximation_lt_one n) x, PolygonalPoint.ext rfl⟩

theorem compactSpace_of_radial_interior (compact : IsCompact s) :
    CompactSpace (PolygonalPoint s) := by
  let := isCompact_iff_compactSpace.mp compact
  exact (radialHomeomorph star radial_interior compact.isBounded).symm.compactSpace

theorem completeSpace_of_radial_interior (compact : IsCompact s) :
    CompleteSpace (PolygonalPoint s) := by
  let := compactSpace_of_radial_interior star radial_interior compact
  infer_instance

/-- The closed region, with its constructed intrinsic metric, completes its interior. -/
def interiorCompletion (compact : IsCompact s) :
    AbstractCompletion (PolygonalPoint (interior s)) where
  space := PolygonalPoint s
  coe := inclusion interior_subset
  uniformStruct := inferInstance
  complete := completeSpace_of_radial_interior star radial_interior compact
  separation := inferInstance
  isUniformInducing := (interior_inclusion_isometry radial_interior).isUniformInducing
  dense := interior_inclusion_dense star radial_interior

end Unfoldings.PolygonalPoint
