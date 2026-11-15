module

public import Unfoldings.Roof.CompletionMesh

/-! Physical cap completions preserving the extended roof on any prescribed compact region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Distant tent supports can be kept inactive beyond the original footprint as well. -/
theorem exists_tent_height_on_compact (L : ℝ) {region : Set Plane}
    (compact : IsCompact region) :
    ∃ H : ℝ, ∀ p ∈ region, K.roofHeight p < H - L * (|p 0| + |p 1|) := by
  have continuous : Continuous (fun p : Plane => K.roofHeight p + L * (|p 0| + |p 1|)) :=
    K.continuous_roofHeight.add
      (continuous_const.mul (((EuclideanSpace.proj 0).continuous.abs).add
        ((EuclideanSpace.proj 1).continuous.abs)))
  obtain ⟨b, bound⟩ := compact.bddAbove_image continuous.continuousOn
  refine ⟨b + 1, ?_⟩
  intro p member
  have upper := bound ⟨p, member, rfl⟩
  linarith

/-- Inactive tent planes preserve the extended supporting-plane roof at the point itself. -/
theorem tentCompletionHeight_eq_of_inactive {H L : ℝ} (nonnegative : 0 ≤ L)
    {p : Plane} (inactive : K.roofHeight p ≤ H - L * (|p 0| + |p 1|)) :
    K.tentCompletionHeight H L p = K.roofHeight p := by
  apply le_antisymm (K.tentCompletionHeight_le_roofHeight H L p)
  obtain ⟨i, equal⟩ := AffineEnvelope.exists_height_eq (K.tentCompletionSupport H L) p
  change K.roofHeight p ≤ AffineEnvelope.height (K.tentCompletionSupport H L) p
  rw [equal]
  cases i with
  | inl f => exact K.roofHeight_le_supportHeight p f
  | inr s => exact inactive.trans (tent_lower_le_support H nonnegative s p)

/-- The constructed cap agrees with the roof throughout the requested region, including
comparison connectors that may lie outside the original footprint. -/
theorem exists_completionMesh_preserving_region {φ : ℝ} (positive : 0 < φ)
    (small : φ < Real.pi / 2) {region : Set Plane} (compact : IsCompact region)
    {J : Type u} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0) :
    ∃ E : K.CompletionMesh φ region extra, ∀ p ∈ region,
      SpatialEnvelope.height (K.completionPlanes E.tentHeight (Real.sin φ / 2)) p =
        K.roofHeight p := by
  let L := Real.sin φ / 2
  have Lpositive : 0 < L := tent_slope_positive positive small
  have compact_union := K.compact_footprint.union compact
  obtain ⟨H, inactive⟩ := K.exists_tent_height_on_compact L compact_union
  obtain ⟨Z₀, _, deep⟩ := K.exists_deep_tentCompletionClip H L 0 compact_union
  let Z := Z₀ - 1
  let family := K.completionPlanes H L
  have heights (p : Plane) : SpatialEnvelope.height family p = K.tentCompletionHeight H L p :=
    K.completionPlanes_envelope H L p
  have preserved (p : Plane) (member : p ∈ K.footprint ∪ region) :
      SpatialEnvelope.height family p = K.roofHeight p :=
    (heights p).trans (K.tentCompletionHeight_eq_of_inactive Lpositive.le (inactive p member).le)
  have equal_clip : SpatialEnvelope.clip family Z = K.tentCompletionClip H L Z := by
    ext p
    change (Z ≤ AffineEnvelope.height (fun i => (family i).height) p) ↔ _
    rw [K.completionPlanes_envelope]
    rfl
  have strict : ∀ p ∈ K.footprint ∪ region, Z < SpatialEnvelope.height family p := by
    intro p member
    have bound := interior_subset (deep member)
    change Z₀ ≤ K.tentCompletionHeight H L p at bound
    rw [heights]
    dsimp [Z]
    linarith
  obtain ⟨q, inside⟩ := K.interior_projection
  have higher := strict q (Or.inl (interior_subset inside))
  have compact_clip : IsCompact (SpatialEnvelope.clip family Z) := by
    rw [equal_clip]
    exact K.isCompact_tentCompletionClip H Lpositive Z
  let T := SpatialEnvelope.constrainedTriangulation family extra proper compact_clip higher
  let E : K.CompletionMesh φ region extra :=
    { tentHeight := H
      level := Z
      mesh := T.refined
      conforming := T.refined_conforming
      covers := fun p member =>
        AffineEnvelope.mem_interior_clip (fun i => (family i).height) (strict p member)
      unchanged := fun p member => preserved p (Or.inl member) }
  exact ⟨E, fun p member => preserved p (Or.inr member)⟩

end Unfoldings.ConvexRoof
