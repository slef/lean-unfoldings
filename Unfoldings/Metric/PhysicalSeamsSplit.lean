module

public import Unfoldings.Metric.PhysicalSeams

/-! Finite closed physical covers split seam domains without changing any declared attachment. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.PhysicalSeams

variable {I J X : Type*} [Finite I] [Finite J] [MetricSpace X] {cells : I → Set X}
  (S : PhysicalSeams cells) (pieces : J → Set X) (closed : ∀ j, IsClosed (pieces j))

/-- Split each physical seam into its intersections with a finite family of closed pieces. -/
def splitClosedSeams : ClosedSeams (fun i => cells i) where
  Seam := (I × I) × J
  Domain := fun p => ↥(S.carrier p.1.1 p.1.2 ∩ pieces p.2)
  left p := p.1.1
  right p := p.1.2
  toLeft p x := ⟨x.val, S.subset_left p.1.1 p.1.2 x.property.1⟩
  toRight p x := ⟨x.val, S.subset_right p.1.1 p.1.2 x.property.1⟩
  left_isometry _ _ _ := rfl
  right_isometry _ _ _ := rfl
  left_closed := by
    intro p
    have equality : Set.range (fun x : ↥(S.carrier p.1.1 p.1.2 ∩ pieces p.2) =>
        (⟨x.val, S.subset_left p.1.1 p.1.2 x.property.1⟩ : cells p.1.1)) =
        {x : cells p.1.1 | x.val ∈ S.carrier p.1.1 p.1.2 ∩ pieces p.2} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro member
        exact ⟨⟨x.val, member⟩, rfl⟩
    rw [equality]
    exact ((S.closed p.1.1 p.1.2).inter (closed p.2)).preimage continuous_subtype_val
  right_closed := by
    intro p
    have equality : Set.range (fun x : ↥(S.carrier p.1.1 p.1.2 ∩ pieces p.2) =>
        (⟨x.val, S.subset_right p.1.1 p.1.2 x.property.1⟩ : cells p.1.2)) =
        {x : cells p.1.2 | x.val ∈ S.carrier p.1.1 p.1.2 ∩ pieces p.2} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro member
        exact ⟨⟨x.val, member⟩, rfl⟩
    rw [equality]
    exact ((S.closed p.1.1 p.1.2).inter (closed p.2)).preimage continuous_subtype_val

/-- A closed cover changes only seam indexing: the exact declared relation is unchanged. -/
theorem splitClosedSeams_relation_iff (cover : (⋃ j, pieces j) = Set.univ)
    (a b : Total (fun i => cells i)) :
    (S.splitClosedSeams pieces closed).relation a b ↔ S.relation a b := by
  constructor
  · rintro ⟨p, x, rfl, rfl⟩
    exact ⟨p.1, ⟨x.val, x.property.1⟩, rfl, rfl⟩
  · rintro ⟨p, x, rfl, rfl⟩
    have covered : x.val ∈ ⋃ j, pieces j := cover.symm ▸ Set.mem_univ x.val
    obtain ⟨j, member⟩ := Set.mem_iUnion.mp covered
    exact ⟨(p, j), ⟨x.val, x.property, member⟩, rfl, rfl⟩

end Unfoldings.MetricGluing.PhysicalSeams
