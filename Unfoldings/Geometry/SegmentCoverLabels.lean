module

public import Unfoldings.Geometry.SegmentCoverDirections
public import Unfoldings.Topology.ClosedCoverValues

/-! A meshed segment stays in one consistently labeled component of a finite segment family. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E I A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Finite I]

/-- Labels agreeing at every geometric contact are constant along every covered segment. -/
theorem segment_cover_labels_eq (first last : I → E) (label : I → A)
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    {a b : E} (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (first i) (last i))
    {i j : I} (at_first : (segment ℝ a b ∩ segment ℝ (first i) (last i)).Nonempty)
    (at_last : (segment ℝ a b ∩ segment ℝ (first j) (last j)).Nonempty) :
    label i = label j := by
  let X := segment ℝ a b
  let := Subtype.preconnectedSpace (convex_segment a b).isPreconnected
  let piece (i : I) : Set X := {x | x.val ∈ segment ℝ (first i) (last i)}
  have closed (i : I) : IsClosed (piece i) := by
    have compact : IsCompact (segment ℝ (first i) (last i)) := by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
    exact compact.isClosed.preimage continuous_subtype_val
  have pieces_cover : (⋃ i, piece i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp (cover x.property)
    exact Set.mem_iUnion.mpr ⟨i, member⟩
  apply eq_of_finite_closed_cover piece closed pieces_cover label
    (fun i j ⟨x, first, last⟩ => compatible i j ⟨x.val, first, last⟩)
  · obtain ⟨x, on_segment, on_piece⟩ := at_first
    exact ⟨⟨x, on_segment⟩, on_piece⟩
  · obtain ⟨x, on_segment, on_piece⟩ := at_last
    exact ⟨⟨x, on_segment⟩, on_piece⟩

/-- One anchor piece selects a single label for the entire whole-edge cover. -/
theorem segment_cover_restrict_label (first last : I → E) (label : I → A)
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    {a b : E} (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (first i) (last i))
    (i : I) (anchor : (segment ℝ a b ∩ segment ℝ (first i) (last i)).Nonempty) :
    segment ℝ a b ⊆ ⋃ j : {j : I // label j = label i}, segment ℝ (first j.val) (last j.val) := by
  intro x member
  obtain ⟨j, on_piece⟩ := Set.mem_iUnion.mp (cover member)
  have equal := segment_cover_labels_eq first last label compatible cover ⟨x, member, on_piece⟩
    anchor
  exact Set.mem_iUnion.mpr ⟨⟨j, equal⟩, on_piece⟩

/-- A genuine outward mesh edge inherits the wedge of the single component it touches. -/
theorem direction_wedge_of_labeled_segment_cover (q a b u v : E) (different : a ≠ b)
    (outward : 0 ≤ inner ℝ (a - q) (b - a)) (first last : I → E) (label : I → A)
    (piece_outward : ∀ i, 0 ≤ inner ℝ (first i - q) (last i - first i))
    (compatible : ∀ i j, (segment ℝ (first i) (last i) ∩
      segment ℝ (first j) (last j)).Nonempty → label i = label j)
    (cover : segment ℝ a b ⊆ ⋃ i, segment ℝ (first i) (last i))
    (i : I) (anchor : (segment ℝ a b ∩ segment ℝ (first i) (last i)).Nonempty)
    (directions : ∀ j, label j = label i → InDirectionWedge u v (last j - first j)) :
    InDirectionWedge u v (b - a) :=
  direction_wedge_of_outward_segment_cover q a b u v different outward
    (fun j : {j : I // label j = label i} => first j.val) (fun j => last j.val)
    (fun j => piece_outward j.val)
    (segment_cover_restrict_label first last label compatible cover i anchor)
    (fun j => directions j.val j.property)

end Unfoldings
