module

public import Unfoldings.Geometry.SolidAngle
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Orthogonal symmetry and null great circles for the volume-induced solid-angle measure. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open MeasureTheory MeasureTheory.Measure
open scoped Pointwise ENNReal NNReal

/-- Orthogonal changes of coordinates preserve actual spherical solid angle. -/
theorem solidAngleMeasure_image (L : Space ≃ₗᵢ[ℝ] Space) {s : Set Space}
    (measurable : MeasurableSet s) (unit : s ⊆ Metric.sphere (0 : Space) 1) :
    solidAngleMeasure (L '' s) = solidAngleMeasure s := by
  have mapped_unit : L '' s ⊆ Metric.sphere (0 : Space) 1 := by
    rintro _ ⟨z, present, rfl⟩
    have normed : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using unit present
    simpa only [Metric.mem_sphere, dist_zero_right, L.norm_map] using normed
  have cone_image : L '' (Set.Ioo (0 : ℝ) 1 • s) = Set.Ioo (0 : ℝ) 1 • (L '' s) := by
    ext z
    constructor
    · rintro ⟨_, ⟨r, bounds, x, present, rfl⟩, rfl⟩
      exact ⟨r, bounds, L x, ⟨x, present, rfl⟩, (map_smul L r x).symm⟩
    · rintro ⟨r, bounds, _, ⟨x, present, rfl⟩, rfl⟩
      exact ⟨r • x, ⟨r, bounds, x, present, rfl⟩, map_smul L r x⟩
  have volume_image (t : Set Space) : volume (L '' t) = volume t := by
    have sets : L '' t = L.symm ⁻¹' t := by
      ext z
      constructor
      · rintro ⟨x, present, rfl⟩
        change L.symm (L x) ∈ t
        rwa [L.symm_apply_apply]
      · intro present
        exact ⟨L.symm z, present, L.apply_symm_apply z⟩
    rw [sets]
    have embedding : MeasurableEmbedding (fun z : Space => L.symm z) := by
      simpa only [LinearIsometryEquiv.coe_toHomeomorph] using
        L.symm.toHomeomorph.measurableEmbedding
    exact L.symm.measurePreserving.measure_preimage_emb embedding t
  have mapped_measurable : MeasurableSet (L '' s) := by
    simpa only [LinearIsometryEquiv.coe_toHomeomorph] using
      L.toHomeomorph.measurableEmbedding.measurableSet_image.mpr measurable
  rw [solidAngleMeasure_apply mapped_measurable mapped_unit,
    solidAngleMeasure_apply measurable unit, ← cone_image, volume_image]

/-- Every great circle has solid angle zero. -/
theorem solidAngleMeasure_hyperplane (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    solidAngleMeasure {z | z ∈ Metric.sphere (0 : Space) 1 ∧ f z = 0} = 0 := by
  have measurable : MeasurableSet {z | z ∈ Metric.sphere (0 : Space) 1 ∧ f z = 0} :=
    (Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : Space) 1)).measurableSet.inter
      (isClosed_eq f.continuous continuous_const).measurableSet
  have unit : {z | z ∈ Metric.sphere (0 : Space) 1 ∧ f z = 0} ⊆
      Metric.sphere (0 : Space) 1 := fun _ present => present.1
  rw [solidAngleMeasure_apply measurable unit]
  have proper : f.toLinearMap.ker ≠ ⊤ := by
    intro equal
    apply nonzero
    ext z
    have present : z ∈ f.toLinearMap.ker := by rw [equal]; trivial
    exact present
  have null := addHaar_submodule volume f.toLinearMap.ker proper
  have included : Set.Ioo (0 : ℝ) 1 • {z | z ∈ Metric.sphere (0 : Space) 1 ∧ f z = 0} ⊆
      (f.toLinearMap.ker : Set Space) := by
    rintro _ ⟨r, _, z, present, rfl⟩
    change f (r • z) = 0
    rw [map_smul, present.2, smul_zero]
  rw [measure_mono_null included null, mul_zero]

/-- Orthogonal symmetry also holds for arbitrary measurable ambient sets. -/
theorem solidAngleMeasure_image_of_measurable (L : Space ≃ₗᵢ[ℝ] Space) {s : Set Space}
    (measurable : MeasurableSet s) : solidAngleMeasure (L '' s) = solidAngleMeasure s := by
  have sets : L '' (s ∩ Metric.sphere (0 : Space) 1) =
      (L '' s) ∩ Metric.sphere (0 : Space) 1 := by
    ext z
    constructor
    · rintro ⟨x, ⟨present, unit⟩, rfl⟩
      refine ⟨⟨x, present, rfl⟩, ?_⟩
      simpa only [Metric.mem_sphere, dist_zero_right, L.norm_map] using unit
    · rintro ⟨⟨x, present, rfl⟩, unit⟩
      refine ⟨x, ⟨present, ?_⟩, rfl⟩
      simpa only [Metric.mem_sphere, dist_zero_right, L.norm_map] using unit
  rw [← solidAngleMeasure_inter_sphere (L '' s), ← sets,
    solidAngleMeasure_image L (measurable.inter Metric.isClosed_sphere.measurableSet)
      Set.inter_subset_right, solidAngleMeasure_inter_sphere]

/-- Every orthogonal coordinate change preserves the complete angular measure. -/
theorem solidAngleMeasure_preserving (L : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving L solidAngleMeasure solidAngleMeasure := by
  refine ⟨L.continuous.measurable, ?_⟩
  apply Measure.ext
  intro s measurable
  rw [Measure.map_apply L.continuous.measurable measurable]
  have sets : L ⁻¹' s = L.symm '' s := by
    ext z
    constructor
    · intro present
      exact ⟨L z, present, L.symm_apply_apply z⟩
    · rintro ⟨x, present, rfl⟩
      change L (L.symm x) ∈ s
      rwa [L.apply_symm_apply]
  rw [sets, solidAngleMeasure_image_of_measurable L.symm measurable]

/-- The full linear hyperplane is null in the ambient presentation of solid angle. -/
theorem solidAngleMeasure_ker (f : Space →L[ℝ] ℝ) (nonzero : f ≠ 0) :
    solidAngleMeasure {z | f z = 0} = 0 := by
  rw [← solidAngleMeasure_inter_sphere]
  have sets : {z : Space | f z = 0} ∩ Metric.sphere (0 : Space) 1 =
      {z | z ∈ Metric.sphere (0 : Space) 1 ∧ f z = 0} := by
    ext z
    exact and_comm
  rw [sets, solidAngleMeasure_hyperplane f nonzero]

end Unfoldings
