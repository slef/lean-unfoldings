module

public import Unfoldings.Roof.NormalRibbonSigns
public import Unfoldings.Geometry.ConvexPacking

/-! Represent signed vertex curvature by bounded densities on normal polygons. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory
open scoped ENNReal BigOperators

namespace Cap

/-- A convex polygon and its interior have the same solid angle. -/
theorem cartesianSolidAngle_image_interior {s : Set Plane}
    (compact : IsCompact s) (convex : Convex ℝ s) :
    cartesianSolidAngle (planeCartesian '' interior s) =
      solidAngleMeasure (gnomonicNormal '' s) := by
  have null : (volume : Measure Plane) (frontier s) = 0 :=
    convex.addHaar_frontier volume
  have mapped_null : (volume.prod volume) (planeCartesian '' frontier s) = 0 := by
    rw [← planeCartesian_preserving.map_eq,
      planeCartesian.measurableEmbedding.map_apply, Set.preimage_image_eq _ planeCartesian.injective, null]
  have weighted_null : cartesianSolidAngle (planeCartesian '' frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ mapped_null
  have eq : planeCartesian '' interior s =
      planeCartesian '' s \ planeCartesian '' frontier s := by
    rw [← Set.image_sdiff planeCartesian.injective]
    congr 1
    ext x
    rw [frontier, compact.isClosed.closure_eq]
    simp only [Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨interior_subset h, fun h' => h'.2 h⟩
    · rintro ⟨member, absent⟩
      by_contra h
      exact absent ⟨member, h⟩
  rw [eq, measure_sdiff_null weighted_null, cartesianSolidAngle_image compact]

/-- The finite signed curvature density in Cartesian normal coordinates. -/
def normalPolygonCharge {V : Type*} [Fintype V] (polygon : V → Set Plane)
    (weight : V → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ v, (planeCartesian '' interior (polygon v)).indicator (fun _ => weight v) z

private theorem image_interior_measurable (s : Set Plane) :
    MeasurableSet (planeCartesian '' interior s) :=
  planeCartesian.measurableSet_image.mpr isOpen_interior.measurableSet

private theorem integrable_indicator_finite {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : Set X} (measured : MeasurableSet s) (finite : μ s < ∞) (c : ℝ) :
    Integrable (s.indicator (fun _ => c)) μ := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  exact (integrable_indicator_iff measured).mpr (integrable_const _)

theorem integrable_normalPolygonCharge {V : Type*} [Fintype V] {cell : Set Plane}
    (finite : cartesianSolidAngle (planeCartesian '' cell) < ∞)
    {polygon : V → Set Plane} (contained : ∀ v, polygon v ⊆ cell) (weight : V → ℝ) :
    Integrable (normalPolygonCharge polygon weight) cartesianSolidAngle := by
  unfold normalPolygonCharge
  refine integrable_finsetSum _ (fun v _ => integrable_indicator_finite
    (image_interior_measurable _) ?_ _)
  exact (measure_mono (Set.image_mono (interior_subset.trans (contained v)))).trans_lt finite

/-- The density integrates to the weighted sum of the polygon solid angles. -/
theorem integral_normalPolygonCharge {V : Type*} [Fintype V] {cell : Set Plane}
    (finite : cartesianSolidAngle (planeCartesian '' cell) < ∞)
    {polygon : V → Set Plane} (contained : ∀ v, polygon v ⊆ cell)
    (compact : ∀ v, IsCompact (polygon v)) (convex : ∀ v, Convex ℝ (polygon v))
    (weight : V → ℝ) :
    (∫ z, normalPolygonCharge polygon weight z ∂cartesianSolidAngle) =
      ∑ v, weight v * (solidAngleMeasure (gnomonicNormal '' polygon v)).toReal := by
  unfold normalPolygonCharge
  rw [integral_finsetSum _ (fun v _ => integrable_indicator_finite
    (image_interior_measurable _) ((measure_mono
      (Set.image_mono (interior_subset.trans (contained v)))).trans_lt finite) _)]
  apply Finset.sum_congr rfl
  intro v _
  rw [integral_indicator (image_interior_measurable _), setIntegral_const,
    smul_eq_mul, Measure.real, cartesianSolidAngle_image_interior (compact v) (convex v), mul_comm]

end Cap
end Unfoldings
