module

public import Unfoldings.Geometry.SpatialEnvelopeCutRays
public import Unfoldings.Geometry.AffineSideRayCells
public import Unfoldings.Metric.AffineCutBanks

/-! Construct and distinguish the two actual metric banks of a whole cut-line tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The two sides of an aligned whole cut line each have a cell containing its entire final tail. -/
theorem exists_opposite_ray_cells (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    (p d : Plane) (on_line : ∀ t : ℝ, f (p + t • d) = 0) :
    ∃ a b : A, signs a = true ∧ signs b = false ∧ ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a ∧ p + t • d ∈ P.footprint b := by
  obtain ⟨a, ha, S, _, tail_a⟩ := AffineArrangement.exists_eventual_ray_cell_on_side
    P.footprint P.closed P.convex P.cover f proper signs aligned p d on_line true
  obtain ⟨b, hb, T, _, tail_b⟩ := AffineArrangement.exists_eventual_ray_cell_on_side
    P.footprint P.closed P.convex P.cover f proper signs aligned p d on_line false
  refine ⟨a, b, ha, hb, max (max S T) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t after
  have both := (le_max_left (max S T) 1).trans after
  exact ⟨tail_a t ((le_max_left S T).trans both),
    tail_b t ((le_max_right S T).trans both)⟩

/-- Opposite physical cell copies remain distinct after cutting a neighborhood of the line. -/
theorem liftCell_ne_of_opposite_sign (cuts : Set Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x)
    {W : Set Plane} (open_W : IsOpen W)
    (cut_level : ∀ x ∈ W, f x = 0 → x ∈ cuts)
    {a b : A} (p : P.footprint a) (q : P.footprint b) (inside : p.val ∈ W)
    (different : signs a ≠ signs b) : P.liftCell cuts a p ≠ P.liftCell cuts b q := by
  let x : P.spatialCell a := P.cellIsometryEquiv a
    ⟨(family (P.support a)).project.symm p.val, p.val, p.property, rfl⟩
  let y : P.spatialCell b := P.cellIsometryEquiv b
    ⟨(family (P.support b)).project.symm q.val, q.val, q.property, rfl⟩
  have spatial_aligned : ∀ a z, z ∈ P.spatialCell a →
      0 ≤ AffineArrangement.signed (f.comp Cap.horizontal.toAffineMap)
        (signs a) z := by
    rintro c z ⟨w, hw, rfl⟩
    have lower := aligned c _ (P.horizontal_mem_footprint c ⟨w, hw⟩)
    simpa only [AffineArrangement.signed_apply, AffineMap.comp_apply,
      LinearMap.coe_toAffineMap] using lower
  have horizontal_x : Cap.horizontal x.val = p.val := by
    change Cap.horizontal ((family (P.support a)).place
      ((family (P.support a)).project.symm p.val)) = p.val
    rw [(family (P.support a)).horizontal_place, (family (P.support a)).project.apply_symm_apply]
  have separated := MetricGluing.cut_of_ne_of_opposite_sign P.spatialCell P.isClosed_spatialCell
    (Cap.horizontal ⁻¹' cuts) (f.comp Cap.horizontal.toAffineMap) signs
    spatial_aligned (open_W.preimage Cap.horizontalCLM.continuous)
    (fun z hz zero => cut_level _ hz zero) x y (by
      change Cap.horizontal x.val ∈ W
      rwa [horizontal_x])
    different
  intro equal
  apply separated
  exact congrArg (P.cutIsometryEquiv cuts) equal

end Unfoldings.SpatialEnvelope.WholePartition
