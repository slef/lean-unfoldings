module

public import Unfoldings.Metric.PhysicalSeams

/-! Labels invariant under actual seam chains distinguish metric copies of a physical point. -/

@[expose] public section

namespace Unfoldings.MetricGluing.PhysicalSeams

variable {I X L : Type*} [Finite I] [MetricSpace X] {cells : I → Set X}
  (S : PhysicalSeams cells)

/-- A cell label preserved by every attachment at a point is preserved by the whole seam class. -/
theorem label_eq_of_eqvGen (label : I → L) (z : X)
    (preserved : ∀ i j, z ∈ S.carrier i j → label i = label j)
    {a b : Total (fun i => cells i)} (related : Relation.EqvGen S.relation a b)
    (at_z : a.2.val = z) : label a.1 = label b.1 := by
  induction related with
  | rel a b joined =>
    obtain ⟨p, x, rfl, rfl⟩ := joined
    exact preserved p.1 p.2 (at_z ▸ x.property)
  | refl => rfl
  | symm a b related ih =>
    exact (ih ((S.physical_eq_of_eqvGen related).trans at_z)).symm
  | trans a b c first last ih_first ih_last =>
    exact (ih_first at_z).trans (ih_last ((S.physical_eq_of_eqvGen first).symm.trans at_z))

/-- Distinct invariant cell labels give distinct actual metric copies, not merely distinct names. -/
theorem of_ne_of_label_ne (label : I → L) (z : X)
    (preserved : ∀ i j, z ∈ S.carrier i j → label i = label j)
    {i j : I} (x : cells i) (y : cells j) (at_z : x.val = z)
    (different : label i ≠ label j) :
    of (fun i => cells i) S.relation i x ≠ of (fun i => cells i) S.relation j y := by
  intro equal
  exact different (S.label_eq_of_eqvGen label z preserved (S.exact _ _ equal) at_z)

end Unfoldings.MetricGluing.PhysicalSeams
