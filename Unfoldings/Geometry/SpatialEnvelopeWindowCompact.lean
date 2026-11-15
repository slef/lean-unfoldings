module

public import Unfoldings.Geometry.SpatialEnvelopeWindowCut

/-! Compact polygonal windows give actual compact original metric cut patches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A] {J : Type*}
  (equations : J → Plane →ᵃ[ℝ] ℝ) (signs : A → J → Bool)
  (aligned : ∀ a z, z ∈ P.footprint a → ∀ j,
    0 ≤ AffineArrangement.signed (equations j) (signs a j) z)

include aligned in
omit [Finite A] in
/-- Every selected original cell lies in the actual closed polygonal window. -/
theorem windowSelected_footprint_subset (a : A) (chosen : WindowSelected signs a) :
    P.footprint a ⊆ {z | ∀ j, 0 ≤ equations j z} := by
  intro z member j
  simpa only [AffineArrangement.signed_apply, chosen j, ↓reduceIte] using aligned a z member j

include aligned in
omit [Finite A] in
/-- Compactness is retained in the actual original spatial support coordinates. -/
theorem windowSpatialCell_compact (compact : IsCompact {z | ∀ j, 0 ≤ equations j z})
    (a : A) (chosen : WindowSelected signs a) : IsCompact (P.spatialCell a) := by
  have compact_footprint : IsCompact (P.footprint a) := compact.of_isClosed_subset (P.closed a)
    (P.windowSelected_footprint_subset equations signs aligned a chosen)
  exact (compact_footprint.image
    (family (P.support a)).project.symm.toAffineMap.continuous_of_finiteDimensional).image
      (family (P.support a)).place.continuous

include aligned in
/-- The intrinsic original window cut is compact, even when cuts disconnect the patch.
No global metric embedding into the full roof is required. -/
theorem windowCut_compactSpace (compact : IsCompact {z | ∀ j, 0 ≤ equations j z})
    (cuts : Set Plane) : CompactSpace (P.WindowCut signs cuts) := by
  let cells := fun a : {a // WindowSelected signs a} => P.spatialCell a.val
  let S := MetricGluing.cutSeams cells (fun a => P.isClosed_spatialCell a.val)
    (Cap.horizontal ⁻¹' cuts)
  have cover : (Set.univ : Set (P.WindowCut signs cuts)) =
      ⋃ a, Set.range (MetricGluing.of (fun a => cells a) S.relation a) := by
    ext x
    constructor
    · intro _
      obtain ⟨⟨a, p⟩, rfl⟩ := MetricGluing.point_surjective (fun a => cells a) S.relation x
      exact Set.mem_iUnion.mpr ⟨a, p, rfl⟩
    · intro _
      exact Set.mem_univ x
  have compact_images (a : {a // WindowSelected signs a}) :
      IsCompact (Set.range (MetricGluing.of (fun a => cells a) S.relation a)) := by
    let : CompactSpace (cells a) := isCompact_iff_compactSpace.mp
      (P.windowSpatialCell_compact equations signs aligned compact a.val a.property)
    exact isCompact_range (MetricGluing.of_lipschitz (fun a => cells a) S.relation a).continuous
  apply isCompact_univ_iff.mp
  rw [cover]
  exact isCompact_iUnion compact_images

end Unfoldings.SpatialEnvelope.WholePartition
