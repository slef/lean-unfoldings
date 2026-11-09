module

public import Unfoldings.Geometry.CompactCollinear
public import Unfoldings.Geometry.LineCoordinate

/-!
# Finite marked vertices for a finite straight-segment network

Mark every original endpoint and both endpoints of every nonempty pairwise
intersection. This includes transverse crossings, coincident segments, partial
collinear overlaps, and isolated degenerate segments.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def segmentCarrier (segments : Set (E × E)) : Set E :=
  ⋃ e ∈ segments, segment ℝ e.1 e.2

theorem segment_subset_line (a b : E) :
    segment ℝ a b ⊆ affineSpan ℝ ({a, b} : Set E) :=
  (affineSpan ℝ ({a, b} : Set E)).convex.segment_subset
    (left_mem_affineSpan_pair ℝ a b) (right_mem_affineSpan_pair ℝ a b)

theorem collinear_segment (a b : E) : Collinear ℝ (segment ℝ a b) := by
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨a, b - a, ?_⟩
  intro x member
  obtain ⟨t, _, rfl⟩ := (segment_eq_image_lineMap ℝ a b).le member
  exact ⟨t, AffineMap.lineMap_apply a b t⟩

theorem compact_segment (a b : E) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem exists_finite_segment_vertices (segments : Set (E × E)) (finite : segments.Finite) :
    ∃ V : Set E, V.Finite ∧ V ⊆ segmentCarrier segments ∧
      (∀ e ∈ segments, e.1 ∈ V ∧ e.2 ∈ V) ∧
      ∀ e ∈ segments, ∀ f ∈ segments,
        (segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2).Nonempty →
          ∃ a ∈ V, ∃ b ∈ V, segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 = segment ℝ a b := by
  let := finite.fintype
  let intersection (p : segments × segments) :=
    segment ℝ p.1.val.1 p.1.val.2 ∩ segment ℝ p.2.val.1 p.2.val.2
  let J := {p : segments × segments // (intersection p).Nonempty}
  have endpoints (j : J) : ∃ a ∈ intersection j.val, ∃ b ∈ intersection j.val,
      intersection j.val = segment ℝ a b := by
    exact exists_segment_of_compact_convex_collinear
      ((compact_segment _ _).inter_right (compact_segment _ _).isClosed)
      ((convex_segment (𝕜 := ℝ) _ _).inter (convex_segment _ _)) j.property
      ((collinear_segment j.val.1.val.1 j.val.1.val.2).subset (fun _ hx => hx.1))
  choose first member_first last member_last equal using endpoints
  let V := Prod.fst '' segments ∪ Prod.snd '' segments ∪ Set.range first ∪ Set.range last
  have finite_V : V.Finite := (((finite.image _).union (finite.image _)).union
    (Set.finite_range _)).union (Set.finite_range _)
  refine ⟨V, finite_V, ?_, ?_, ?_⟩
  · intro x member
    rcases member with ((⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩
    · exact Set.mem_iUnion₂.mpr ⟨e, he, left_mem_segment ℝ e.1 e.2⟩
    · exact Set.mem_iUnion₂.mpr ⟨e, he, right_mem_segment ℝ e.1 e.2⟩
    · exact Set.mem_iUnion₂.mpr ⟨j.val.1.val, j.val.1.property, (member_first j).1⟩
    · exact Set.mem_iUnion₂.mpr ⟨j.val.1.val, j.val.1.property, (member_last j).1⟩
  · intro e he
    exact ⟨Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩)),
      Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))⟩
  · intro e he f hf nonempty
    let j : J := ⟨(⟨e, he⟩, ⟨f, hf⟩), nonempty⟩
    exact ⟨first j, Or.inl (Or.inr ⟨j, rfl⟩), last j, Or.inr ⟨j, rfl⟩, equal j⟩

end Unfoldings
