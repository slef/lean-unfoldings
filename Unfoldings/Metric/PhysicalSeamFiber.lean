module

public import Unfoldings.Metric.PhysicalSeams

/-! Local physical seam agreement preserves entire metric fibers when other cuts are restored. -/

@[expose] public section

namespace Unfoldings.MetricGluing.PhysicalSeams

variable {I X : Type*} [Finite I] [MetricSpace X] {cells : I → Set X}
  (S T : PhysicalSeams cells)

/-- An attachment chain at one physical point uses only the carrier germs at that point. -/
theorem eqvGen_of_carriers_at (z : X)
    (agreement : ∀ i j, z ∈ T.carrier i j → z ∈ S.carrier i j)
    {a b : Total (fun i => cells i)} (related : Relation.EqvGen T.relation a b)
    (position : a.2.val = z) : Relation.EqvGen S.relation a b := by
  induction related with
  | rel a b joined =>
    obtain ⟨p, x, rfl, rfl⟩ := joined
    exact Relation.EqvGen.rel _ _
      ⟨p, ⟨x.val, position.symm ▸ agreement p.1 p.2 (position ▸ x.property)⟩, rfl, rfl⟩
  | refl => exact Relation.EqvGen.refl _
  | symm a b related ih =>
    exact (ih ((T.physical_eq_of_eqvGen related).trans position)).symm
  | trans a b c first last ih_first ih_last =>
    exact Relation.EqvGen.trans _ _ _ (ih_first position)
      (ih_last ((T.physical_eq_of_eqvGen first).symm.trans position))

/-- Restoring distant seams cannot merge any actual copies in a fiber whose carriers agree.
Unlike a ball chart, this rules out competing preimages arbitrarily far away in the cut metric. -/
theorem forget_injective_at_of_carriers
    (included : ∀ i j, S.carrier i j ⊆ T.carrier i j)
    (x : Realization (fun i => cells i) S.relation)
    (agreement : ∀ i j, S.fold x ∈ T.carrier i j → S.fold x ∈ S.carrier i j)
    (y : Realization (fun i => cells i) S.relation)
    (equal : forget (fun i => cells i) (S.relation_mono included) x =
      forget (fun i => cells i) (S.relation_mono included) y) : x = y := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) S.relation x
  obtain ⟨b, rfl⟩ := point_surjective (fun i => cells i) S.relation y
  apply point_eq_of_eqvGen (fun i => cells i)
  apply S.eqvGen_of_carriers_at T a.2.val agreement _ rfl
  exact T.exact a b equal

end Unfoldings.MetricGluing.PhysicalSeams
