module

public import Unfoldings.Topology.PlanarOpenMapping

/-! A compactly controlled planar embedding carries an open set's exact frontier to its image. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

theorem isOpen_complex_range_of_continuous_injective {U : Set ℂ} (opened : IsOpen U)
    (f : C(U, ℂ)) (injective : Function.Injective f) : IsOpen (Set.range f) := by
  let g : C(U, Plane) := ⟨fun z => complexIsometry (f z),
    complexIsometry.continuous.comp f.continuous⟩
  have embedding : Topology.IsOpenEmbedding (fun z : U => complexIsometry z.val) :=
    complexIsometry.toHomeomorph.isOpenEmbedding.comp opened.isOpenEmbedding_subtypeVal
  have open_range := isOpen_range_of_openEmbedding _ embedding g
    (complexIsometry.injective.comp injective)
  have preimage : complexIsometry ⁻¹' Set.range g = Set.range f := by
    ext x
    constructor
    · rintro ⟨z, equal⟩
      exact ⟨z, complexIsometry.injective equal⟩
    · rintro ⟨z, equal⟩
      exact ⟨z, congrArg complexIsometry equal⟩
  simpa only [preimage] using open_range.preimage complexIsometry.continuous

/-- Compact closure prevents boundary values escaping the trace. Injectivity on
that whole closure excludes a bank value from the image interior. -/
theorem frontier_image_open_eq {U : Set ℂ} (opened : IsOpen U)
    (compact : IsCompact (closure U)) {f : ℂ → ℂ} (continuous : Continuous f)
    (injective : Set.InjOn f (closure U)) : frontier (f '' U) = f '' frontier U := by
  let patch : C(U, ℂ) := ⟨fun z => f z.val, continuous.comp continuous_subtype_val⟩
  have patch_injective : Function.Injective patch := by
    intro x y equal
    exact Subtype.ext (injective (subset_closure x.property) (subset_closure y.property) equal)
  have open_image : IsOpen (f '' U) := by
    have same : Set.range patch = f '' U := by
      ext y
      constructor
      · rintro ⟨z, equal⟩
        exact ⟨z.val, z.property, equal⟩
      · rintro ⟨z, member, equal⟩
        exact ⟨⟨z, member⟩, equal⟩
    rw [← same]
    exact isOpen_complex_range_of_continuous_injective opened patch patch_injective
  have closure_image : closure (f '' U) = f '' closure U := by
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono subset_closure)
        (compact.image continuous).isClosed
    · exact image_closure_subset_closure_image continuous
  apply Set.Subset.antisymm
  · intro y boundary
    obtain ⟨x, member, equal⟩ := closure_image.subset boundary.1
    refine ⟨x, ⟨member, ?_⟩, equal⟩
    intro interior
    have image_member : y ∈ f '' U := ⟨x, interior_subset interior, equal⟩
    exact boundary.2 (open_image.interior_eq.symm ▸ image_member)
  · rintro y ⟨x, boundary, rfl⟩
    refine ⟨closure_image.symm.subset ⟨x, boundary.1, rfl⟩, ?_⟩
    intro interior
    obtain ⟨z, member, equal⟩ := interior_subset interior
    have same : z = x := injective (subset_closure member) boundary.1 equal
    exact boundary.2 (opened.interior_eq.symm ▸ (same ▸ member))

end Unfoldings.PlanarTopology
