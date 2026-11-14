module

public import Unfoldings.Geometry.AffineArrangement

/-! Finite convex-cell decompositions of regular closed sets, including unbounded ones. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineArrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]

/-- Boundary supports construct actual full-dimensional cells; compactness is unnecessary. -/
theorem exists_finite_unbounded_chamber_cover (f : ι → E →ᵃ[ℝ] ℝ)
    (nonzero : ∀ i, f i ≠ 0) {s : Set E} (closed : IsClosed s)
    (regular_closed : closure (interior s) = s)
    (support : ∀ x ∈ frontier s, ∃ i, f i x = 0) :
    ∃ S : Set (ι → Bool), S.Finite ∧
      (∀ signs ∈ S, (chamber f signs).Nonempty ∧ chamber f signs ⊆ interior s) ∧
      s = ⋃ signs ∈ S, closedChamber f signs := by
  let S := {signs | (chamber f signs ∩ interior s).Nonempty}
  have finite : S.Finite := Set.toFinite _
  have contained (signs : ι → Bool) (member : signs ∈ S) : chamber f signs ⊆ interior s :=
    chamber_subset_interior f support signs member
  have nonempty (signs : ι → Bool) (member : signs ∈ S) : (chamber f signs).Nonempty :=
    member.mono (fun _ hx => hx.1)
  have closed_contained (signs : ι → Bool) (member : signs ∈ S) : closedChamber f signs ⊆ s := by
    rw [← closure_chamber f signs (nonempty signs member)]
    exact closure_minimal ((contained signs member).trans interior_subset) closed
  let cover := ⋃ signs ∈ S, closedChamber f signs
  have closed_cover : IsClosed cover :=
    finite.isClosed_biUnion (fun signs _ => isClosed_closedChamber f signs)
  have regular_covered : interior s ∩ {x | ∀ i, f i x ≠ 0} ⊆ cover := by
    intro x hx
    obtain ⟨signs, member⟩ := exists_chamber_of_regular f hx.2
    exact Set.mem_iUnion.mpr ⟨signs, Set.mem_iUnion.mpr
      ⟨⟨x, member, hx.1⟩, fun i => (member i).le⟩⟩
  have interior_covered : interior s ⊆ cover :=
    ((dense_regular f nonzero).open_subset_closure_inter isOpen_interior).trans
      (closure_minimal regular_covered closed_cover)
  refine ⟨S, finite, fun signs member => ⟨nonempty signs member, contained signs member⟩,
    Set.Subset.antisymm ?_ ?_⟩
  · rw [← regular_closed]
    exact closure_minimal interior_covered closed_cover
  · intro x hx
    obtain ⟨signs, member, point⟩ := Set.mem_iUnion₂.mp hx
    exact closed_contained signs member point

/-- Distinct full-dimensional chamber cells have disjoint actual interiors. -/
theorem disjoint_chamber_interiors (f : ι → E →ᵃ[ℝ] ℝ) {a b : ι → Bool}
    (ha : (chamber f a).Nonempty) (hb : (chamber f b).Nonempty) (different : a ≠ b) :
    Disjoint (interior (closedChamber f a)) (interior (closedChamber f b)) := by
  rw [interior_closedChamber f a ha, interior_closedChamber f b hb]
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact different (chamber_signs_unique f hx hy)

end Unfoldings.AffineArrangement
