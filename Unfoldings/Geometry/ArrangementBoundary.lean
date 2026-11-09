module

public import Unfoldings.Geometry.AffineArrangement

/-!
# Finite convex pieces of an affine-arrangement boundary

The closure of the complement is covered by the closures of its open chambers.
Intersect these with the inside chambers. Every resulting boundary piece is
compact and convex and lies in a genuine affine hyperplane.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.AffineArrangement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]

theorem closure_complement_chamber_cover (f : ι → E →ᵃ[ℝ] ℝ)
    (nonzero : ∀ i, f i ≠ 0) {s : Set E} (closed : IsClosed s)
    (support : ∀ x ∈ frontier s, ∃ i, f i x = 0) :
    ∃ T : Set (ι → Bool), T.Finite ∧
      (∀ signs ∈ T, (chamber f signs).Nonempty ∧ chamber f signs ⊆ sᶜ) ∧
      closure sᶜ = ⋃ signs ∈ T, closedChamber f signs := by
  let T := {signs | (chamber f signs ∩ sᶜ).Nonempty}
  have finite : T.Finite := Set.toFinite _
  have nonempty (signs : ι → Bool) (member : signs ∈ T) : (chamber f signs).Nonempty :=
    member.mono (fun _ hx => hx.1)
  have contained (signs : ι → Bool) (member : signs ∈ T) : chamber f signs ⊆ sᶜ := by
    have support_complement : ∀ x ∈ frontier sᶜ, ∃ i, f i x = 0 := by
      rwa [frontier_compl]
    have meets : (chamber f signs ∩ interior sᶜ).Nonempty := by
      rwa [closed.isOpen_compl.interior_eq]
    exact (chamber_subset_interior f support_complement signs meets).trans interior_subset
  let cover := ⋃ signs ∈ T, closedChamber f signs
  have closed_cover : IsClosed cover :=
    finite.isClosed_biUnion (fun signs _ => isClosed_closedChamber f signs)
  have regular_covered : sᶜ ∩ {x | ∀ i, f i x ≠ 0} ⊆ cover := by
    intro x hx
    obtain ⟨signs, member⟩ := exists_chamber_of_regular f hx.2
    exact Set.mem_iUnion.mpr ⟨signs, Set.mem_iUnion.mpr
      ⟨⟨x, member, hx.1⟩, fun i => (member i).le⟩⟩
  have complement_covered : sᶜ ⊆ cover :=
    ((dense_regular f nonzero).open_subset_closure_inter closed.isOpen_compl).trans
      (closure_minimal regular_covered closed_cover)
  refine ⟨T, finite, fun signs member => ⟨nonempty signs member, contained signs member⟩,
    Set.Subset.antisymm (closure_minimal complement_covered closed_cover) ?_⟩
  intro x hx
  obtain ⟨signs, member, point⟩ := Set.mem_iUnion₂.mp hx
  have included : closedChamber f signs ⊆ closure sᶜ := by
    rw [← closure_chamber f signs (nonempty signs member)]
    exact closure_mono (contained signs member)
  exact included point

omit [FiniteDimensional ℝ E] [Finite ι] in
theorem closed_chamber_intersection_zero (f : ι → E →ᵃ[ℝ] ℝ)
    {a b : ι → Bool} (different : a ≠ b) :
    ∃ i, ∀ x ∈ closedChamber f a ∩ closedChamber f b, f i x = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp (fun equal => different (funext equal))
  refine ⟨i, ?_⟩
  intro x hx
  have ha := hx.1 i
  have hb := hx.2 i
  cases h_a : a i <;> cases h_b : b i
  all_goals simp only [h_a, h_b, not_true_eq_false] at hi
  all_goals simp only [signed_apply, h_a, h_b, Bool.false_eq_true, ↓reduceIte] at ha hb
  all_goals linarith

theorem chamber_nonempty_of_interior_closedChamber (f : ι → E →ᵃ[ℝ] ℝ)
    (nonzero : ∀ i, f i ≠ 0) (signs : ι → Bool)
    (nonempty : (interior (closedChamber f signs)).Nonempty) : (chamber f signs).Nonempty := by
  obtain ⟨x, inside, regular⟩ :=
    (dense_regular f nonzero).inter_open_nonempty _ isOpen_interior nonempty
  refine ⟨x, ?_⟩
  have weak := interior_subset inside
  intro i
  have neq : signed (f i) (signs i) x ≠ 0 := by
    have hi := regular i
    cases h : signs i <;> simpa [h] using hi
  exact lt_of_le_of_ne (weak i) neq.symm

theorem exists_boundary_chamber_cover (f : ι → E →ᵃ[ℝ] ℝ)
    (nonzero : ∀ i, f i ≠ 0) {s : Set E} (closed : IsClosed s)
    (support : ∀ x ∈ frontier s, ∃ i, f i x = 0)
    (S : Set (ι → Bool)) (included : ∀ a ∈ S, closedChamber f a ⊆ s)
    (cover : s = ⋃ a ∈ S, closedChamber f a) :
    ∃ T : Set (ι → Bool), T.Finite ∧
      frontier s = ⋃ a ∈ S, ⋃ b ∈ T, closedChamber f a ∩ closedChamber f b ∧
      ∀ a ∈ S, ∀ b ∈ T, ∃ i,
        ∀ x ∈ closedChamber f a ∩ closedChamber f b, f i x = 0 := by
  obtain ⟨T, finite_T, outside, complement_cover⟩ :=
    closure_complement_chamber_cover f nonzero closed support
  refine ⟨T, finite_T, ?_, ?_⟩
  · ext x
    rw [frontier_eq_closure_inter_closure, closed.closure_eq]
    constructor
    · intro hx
      obtain ⟨a, ha, xa⟩ := Set.mem_iUnion₂.mp (cover ▸ hx.1)
      obtain ⟨b, hb, xb⟩ := Set.mem_iUnion₂.mp (complement_cover ▸ hx.2)
      exact Set.mem_iUnion₂.mpr ⟨a, ha, Set.mem_iUnion₂.mpr ⟨b, hb, xa, xb⟩⟩
    · intro hx
      obtain ⟨a, ha, member⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨b, hb, xa, xb⟩ := Set.mem_iUnion₂.mp member
      refine ⟨included a ha xa, ?_⟩
      rw [complement_cover]
      exact Set.mem_iUnion₂.mpr ⟨b, hb, xb⟩
  · intro a ha b hb
    apply closed_chamber_intersection_zero f
    intro equal
    obtain ⟨x, hx⟩ := (outside b hb).1
    have in_complement := (outside b hb).2 hx
    have in_closed : x ∈ closedChamber f a := by
      rw [equal]
      exact fun i => (hx i).le
    exact in_complement (included a ha in_closed)

theorem frontier_support_of_chamber_cover (f : ι → E →ᵃ[ℝ] ℝ) {s : Set E}
    (closed : IsClosed s) (S : Set (ι → Bool))
    (included : ∀ a ∈ S, closedChamber f a ⊆ s)
    (cover : s = ⋃ a ∈ S, closedChamber f a) :
    ∀ x ∈ frontier s, ∃ i, f i x = 0 := by
  intro x hx
  obtain ⟨a, ha, member⟩ := Set.mem_iUnion₂.mp (cover ▸ closed.frontier_subset hx)
  by_contra regular
  have strict : x ∈ chamber f a := by
    intro i
    have nonzero : f i x ≠ 0 := fun zero => regular ⟨i, zero⟩
    have signed_nonzero : signed (f i) (a i) x ≠ 0 := by
      cases h : a i <;> simpa [h] using nonzero
    exact lt_of_le_of_ne (member i) signed_nonzero.symm
  have weak : chamber f a ⊆ closedChamber f a := fun _ hz i => (hz i).le
  have inside : chamber f a ⊆ interior s :=
    interior_maximal (weak.trans (included a ha)) (isOpen_chamber f a)
  exact hx.2 (inside strict)

end Unfoldings.AffineArrangement
