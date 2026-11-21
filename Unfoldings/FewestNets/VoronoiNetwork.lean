module

public import Unfoldings.FewestNets.VoronoiLabel
public import Unfoldings.FewestNets.EndpointCrossingLocality
public import Unfoldings.Geometry.SphericalConvex

/-! Data and basic geometry for a fixed spherical Voronoi network. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry SpatialRotation
open scoped BigOperators

/-- Geometric hypotheses for a finite family of Voronoi sites and an indexed
family of minor arcs covering all its walls. -/
structure VoronoiNetwork {I J : Type*} (site : I → Space)
    (endpoint : J → Bool → Space) (separation incidentAngle : ℝ) : Prop where
  siteInjective : Function.Injective site
  siteUnit : ∀ i, ‖site i‖ = 1
  coversHemisphere : ∀ x : Space, ‖x‖ = 1 → ∃ i, 0 < inner ℝ x (site i)
  coversWalls : voronoiWalls site ⊆ ⋃ j, networkEdge endpoint j
  edgeUnit : ∀ j b, ‖endpoint j b‖ = 1
  edgePositive : ∀ j, 0 < angle (endpoint j false) (endpoint j true)
  edgeShort : ∀ j, angle (endpoint j false) (endpoint j true) ≤ Real.pi / 2
  separated : ∀ ⦃i j⦄, i ≠ j → (∀ a b, endpoint i a ≠ endpoint j b) →
    ∀ x ∈ networkEdge endpoint i, ∀ y ∈ networkEdge endpoint j, separation ≤ angle x y
  incident : ∀ ⦃i j a b⦄, i ≠ j → endpoint i a = endpoint j b →
    incidentAngle ≤ angle (minorArcTangent (endpoint i a) (endpoint i (!a)))
      (minorArcTangent (endpoint j b) (endpoint j (!b)))
  separationPositive : 0 < separation
  separationSmall : separation ≤ 1 / 2
  incidentPositive : 0 < incidentAngle
  incidentSmall : incidentAngle ≤ Real.pi

/-- The actual closed spherical cell, as opposed to its open cone of unique labels. -/
def sphericalVoronoiCell {I : Type*} (site : I → Space) (i : I) : Set Space :=
  finiteHullNormalCone site i ∩ Metric.sphere 0 1

variable {I J : Type*} {site : I → Space} {endpoint : J → Bool → Space}
  {separation incidentAngle : ℝ}

theorem isClosed_sphericalVoronoiCell (site : I → Space) (i : I) :
    IsClosed (sphericalVoronoiCell site i) :=
  (isClosed_finiteHullNormalCone site i).inter Metric.isClosed_sphere

theorem sphericalConvex_sphericalVoronoiCell (site : I → Space) (i : I) :
    SphericalConvex (sphericalVoronoiCell site i) := by
  constructor
  · intro z hz
    simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
  · intro x hx y hy a b ha hb ne
    constructor
    · intro j
      have hxj : inner ℝ x (site j) ≤ inner ℝ x (site i) := hx.1 j
      have hyj : inner ℝ y (site j) ≤ inner ℝ y (site i) := hy.1 j
      simp only [NormedSpace.normalize, real_inner_smul_left, inner_add_left]
      exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hxj ha)
        (mul_le_mul_of_nonneg_left hyj hb)) (inv_nonneg.mpr (norm_nonneg _))
    · simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize ne

/-- The rotated site itself centers its closed cell in an open hemisphere. -/
theorem VoronoiNetwork.rotated_hemisphere
    (H : VoronoiNetwork site endpoint separation incidentAngle)
    (g : SpatialRotation) (i : I) (x : Space)
    (inside : x ∈ sphericalVoronoiCell (fun j => linear g (site j)) i) :
    0 < inner ℝ (linear g (site i)) x := by
  let L := isometry g
  let y := L.symm x
  have unit : ‖y‖ = 1 := by
    rw [L.symm.norm_map]
    simpa only [Metric.mem_sphere, dist_zero_right] using inside.2
  obtain ⟨j, positive⟩ := H.coversHemisphere y unit
  have rotated : 0 < inner ℝ x (linear g (site j)) := by
    have h := L.inner_map_map y (site j)
    change inner ℝ (L y) (linear g (site j)) = _ at h
    rw [L.apply_symm_apply] at h
    rwa [h]
  rw [real_inner_comm]
  exact rotated.trans_le (inside.1 j)

variable [Finite I] [Nonempty I]

/-- At a uniquely labeled normal, membership in a closed Voronoi cell is
equivalent to its chosen label. -/
theorem mem_sphericalVoronoiCell_iff_voronoiLabel (injective : Function.Injective site)
    (g : SpatialRotation) {x : Space} (unit : ‖x‖ = 1)
    (unique : x ∈ strictVoronoiCone (fun j => linear g (site j)) (voronoiLabel site x g))
    (i : I) : x ∈ sphericalVoronoiCell (fun j => linear g (site j)) i ↔
      voronoiLabel site x g = i := by
  constructor
  · intro inside
    by_contra diff
    have inj_rot : Function.Injective (fun j => linear g (site j)) :=
      (isometry g).injective.comp injective
    have separated := (mem_interior_finiteHullNormalCone_iff inj_rot _).mp unique i (Ne.symm diff)
    exact (not_lt_of_ge (inside.1 (voronoiLabel site x g))) separated
  · rintro rfl
    exact ⟨interior_subset unique, by simpa only [Metric.mem_sphere, dist_zero_right] using unit⟩

theorem ae_voronoiLabel_mem_strict (injective : Function.Injective site)
    {V : Type*} [Finite V] (point : V → Space) (unit : ∀ v, ‖point v‖ = 1) :
    ∀ᵐ g ∂probability, ∀ v,
      point v ∈ strictVoronoiCone (fun j => linear g (site j)) (voronoiLabel site (point v) g) := by
  filter_upwards [ae_unique_strictVoronoiCone site injective point unit] with g unique
  intro v
  obtain ⟨i, inside, _⟩ := unique v
  rw [voronoiLabel_eq_of_mem_strictVoronoiCone site injective _ _ _ inside]
  exact inside

end Unfoldings.FewestNets
