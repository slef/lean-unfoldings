module

public import Unfoldings.FewestNets.SphericalSelectorMetric
public import Unfoldings.FewestNets.OrthogonalSiteFlags
public import Unfoldings.Geometry.SphericalRotation

/-! Place an entire spherical selector, retaining its actual supporting and angular data. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open SpatialRotation InnerProductGeometry

/-- Orthogonal coordinates carry open minor arcs to open minor arcs. -/
theorem image_openMinorArc_linearIsometry (T : Space ≃ₗᵢ[ℝ] Space) (u v : Space) :
    T '' openMinorArc u v = openMinorArc (T u) (T v) := by
  have map_point (t : ℝ) :
      T (NormedSpace.normalize ((1 - t) • u + t • v)) =
        NormedSpace.normalize ((1 - t) • T u + t • T v) := by
    rw [← normalize_linearIsometry, map_add, map_smul, map_smul]
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (map_point t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, map_point t⟩

/-- An orthogonal change of coordinates carries the actual minor-arc tangent. -/
theorem map_minorArcTangent (T : Space ≃ₗᵢ[ℝ] Space) (u v : Space) :
    T (minorArcTangent u v) = minorArcTangent (T u) (T v) := by
  have angle_map : angle (T u) (T v) = angle u v := T.toLinearIsometry.angle_map _ _
  simp only [minorArcTangent, map_smul, map_sub, angle_map]

namespace SpatialRotation

/-- Inversion in either orientation class is inversion of the rotation. -/
theorem orthogonalIsometry_symm (g : SpatialRotation) (b : Bool) :
    (orthogonalIsometry g b).symm = orthogonalIsometry g⁻¹ b := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (orthogonalIsometry g b).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [orthogonalIsometry_apply]
  cases b
  · exact (linear_apply_inv _ _).symm
  · change x = -(linear g (-(linear g⁻¹ x)))
    rw [map_neg, neg_neg, linear_apply_inv]

/-- Either orientation class almost surely avoids any finite family of
genuine great circles for any finite family of unit directions. -/
theorem ae_orthogonalIsometry_avoids_hyperplanes {I J : Type*} [Finite I] [Finite J]
    (b : Bool) (point : I → Space) (unit : ∀ i, ‖point i‖ = 1)
    (form : J → Space →ₗ[ℝ] ℝ) (nonzero : ∀ j, form j ≠ 0) :
    ∀ᵐ g ∂probability, ∀ i j, form j (orthogonalIsometry g b (point i)) ≠ 0 := by
  have h := ae_avoids_finite_hyperplanes point unit (fun j => (form j).toContinuousLinearMap)
    (fun j zero => nonzero j (by
      ext x
      exact DFunLike.congr_fun zero x))
  filter_upwards [h] with g avoids i j
  cases b
  · exact avoids i j
  · change form j (-(linear g (point i))) ≠ 0
    rw [map_neg, neg_ne_zero]
    exact avoids i j

/-- The corresponding pulled-back unit directions also avoid those
great circles almost surely. -/
theorem ae_orthogonalIsometry_symm_avoids_hyperplanes {I J : Type*} [Finite I] [Finite J]
    (b : Bool) (point : I → Space) (unit : ∀ i, ‖point i‖ = 1)
    (form : J → Space →ₗ[ℝ] ℝ) (nonzero : ∀ j, form j ≠ 0) :
    ∀ᵐ g ∂probability, ∀ i j, form j ((orthogonalIsometry g b).symm (point i)) ≠ 0 := by
  have probability_inv : MeasureTheory.MeasurePreserving (fun g : SpatialRotation => g⁻¹)
      probability probability := MeasureTheory.Measure.measurePreserving_inv probability
  have h := probability_inv.quasiMeasurePreserving.ae
    (ae_orthogonalIsometry_avoids_hyperplanes b point unit form nonzero)
  simpa only [orthogonalIsometry_symm] using h

end SpatialRotation

namespace FewestNets.SphericalSelectorBoundary

variable {J : Type*} {region : Set Space} (B : SphericalSelectorBoundary J region)

/-- The literal selector arcs and support equations commute with placement. -/
def map (T : Space ≃ₗᵢ[ℝ] Space) : SphericalSelectorBoundary J (T '' region) where
  endpoint j b := T (B.endpoint j b)
  form j := (B.form j).comp T.symm.toLinearEquiv.toLinearMap
  form_ne_zero j := by
    intro zero
    apply B.form_ne_zero j
    ext x
    change B.form j x = 0
    have h := DFunLike.congr_fun zero (T x)
    change B.form j (T.symm (T x)) = 0 at h
    simpa only [T.symm_apply_apply] using h
  membership x := by
    constructor
    · rintro ⟨u, inside, rfl⟩
      have h := (B.membership u).mp inside
      refine ⟨(T.norm_map u).trans h.1, fun j => ?_⟩
      change 0 ≤ B.form j (T.symm (T u))
      rw [T.symm_apply_apply]
      exact h.2 j
    · rintro ⟨unit, forms⟩
      exact ⟨T.symm x, (B.membership _).mpr ⟨(T.symm.norm_map _).trans unit, forms⟩,
        T.apply_symm_apply x⟩
  activeSide j := by
    rw [← image_closedMinorArc_linearIsometry, ← B.activeSide]
    ext x
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hz⟩
      change B.form j (T.symm (T u)) = 0 at hz
      exact ⟨u, ⟨hu, by rwa [T.symm_apply_apply] at hz⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hz⟩, rfl⟩
      refine ⟨⟨u, hu, rfl⟩, ?_⟩
      change B.form j (T.symm (T u)) = 0
      rw [T.symm_apply_apply]
      exact hz

namespace MetricData

variable {B}

-- The supports and the endpoints are mapped by the very same isometry.
/-- All of the angular hypotheses of the sharp crossing estimate commute with placement. -/
def map (M : MetricData B) (T : Space ≃ₗᵢ[ℝ] Space) : MetricData (B.map T) where
  longest := M.longest
  longest_pos := M.longest_pos
  longest_small := M.longest_small
  side_pos j := (T.toLinearIsometry.angle_map _ _).symm ▸ M.side_pos j
  side_le j := (T.toLinearIsometry.angle_map _ _).symm ▸ M.side_le j
  separation := M.separation
  separation_pos := M.separation_pos
  separation_small := M.separation_small
  separated := by
    intro i j different nonincident x hx y hy
    change x ∈ closedMinorArc (T (B.endpoint i false)) (T (B.endpoint i true)) at hx
    change y ∈ closedMinorArc (T (B.endpoint j false)) (T (B.endpoint j true)) at hy
    rw [← image_closedMinorArc_linearIsometry] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact (M.separated different (fun a b same => nonincident a b (congrArg T same)) u hu v hv).trans_eq
      (T.toLinearIsometry.angle_map u v).symm
  corner := M.corner
  corner_pos := M.corner_pos
  incident := by
    intro i j a b different shared
    change M.corner i a ≤
      angle (minorArcTangent (T (B.endpoint i a)) (T (B.endpoint i (!a))))
        (minorArcTangent (T (B.endpoint j b)) (T (B.endpoint j (!b))))
    rw [← map_minorArcTangent, ← map_minorArcTangent]
    exact (M.incident different (T.injective shared)).trans_eq (T.toLinearIsometry.angle_map _ _).symm

end MetricData
end FewestNets.SphericalSelectorBoundary
end Unfoldings
