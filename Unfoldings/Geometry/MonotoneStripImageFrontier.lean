module

public import Unfoldings.Geometry.MonotoneStripTopology
public import Unfoldings.Topology.CompactImageFrontier

/-! The whole developed strip-image frontier consists of actual bank traces and end-level values. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem frontier_image_openSlab_eq (a b : ℝ) {G : ℂ → ℂ} (continuous : Continuous G)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b})) :
    frontier (G '' S.openSlab a b) = G '' frontier (S.openSlab a b) := by
  apply PlanarTopology.frontier_image_open_eq (S.isOpen_openSlab a b)
    (S.isCompact_closure_openSlab a b) continuous
  have inside : S.openSlab a b ⊆ {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} :=
    fun _ member => ⟨member.1, member.2.1.le, member.2.2.le⟩
  exact injective.mono (closure_mono inside)

/-- The image boundary has no hidden component: every point is an actual lower or
upper bank trace, or a value at one of the two physical end levels. -/
theorem frontier_image_openSlab_cases (a b : ℝ) {G : ℂ → ℂ} (continuous : Continuous G)
    (injective : Set.InjOn G
      (closure {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b}))
    {y : ℂ} (boundary : y ∈ frontier (G '' S.openSlab a b)) :
    (∃ h ∈ Set.Icc a b, G (S.lower.point h) = y) ∨
    (∃ h ∈ Set.Icc a b, G (S.upper.point h) = y) ∨
    (∃ z ∈ S.boundedCarrier a b, z.re + z.im = a ∧ G z = y) ∨
    (∃ z ∈ S.boundedCarrier a b, z.re + z.im = b ∧ G z = y) := by
  obtain ⟨z, at_boundary, value⟩ := (S.frontier_image_openSlab_eq a b continuous injective).subset
    boundary
  have member := S.closure_openSlab_subset a b at_boundary.1
  rcases S.frontier_openSlab_cases a b at_boundary with lower | upper | first | last
  · exact Or.inl ⟨z.re + z.im, member.2, lower ▸ value⟩
  · exact Or.inr (Or.inl ⟨z.re + z.im, member.2, upper ▸ value⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨z, member, first, value⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨z, member, last, value⟩))

end Unfoldings.MonotoneStrip
