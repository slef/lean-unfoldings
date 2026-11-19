module

public import Unfoldings.Metric.MappedBankGraftExactness
public import Unfoldings.Metric.ClosedSeams
public import Unfoldings.Metric.ChangeSeams

/-! A small graft ball lifts to whole original piece balls around its actual class. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {I : Type*} {J : I → Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)]
  {B : Type*} {Parameter : B → Type*} {V : Type*} [MetricSpace V]
  (cells : ∀ i, J i → Set V)
  (inner : ∀ i, Total (fun j => cells i j) → Total (fun j => cells i j) → Prop)
  (coordinates : ∀ i, Realization (fun j => cells i j) (inner i) ≃ᵢ X i)
  (left right : ∀ b, Parameter b → Total X)

local notation "E" => NestedCell (fun i j => cells i j)
local notation "Restore" => mappedNestedPoint cells inner coordinates
local notation "Banks" => bankSeams left right

/-- Every nearby whole-piece representative is intrinsically close to an actual
representative of the center in that same piece. All original piece tags are retained. -/
theorem exists_mappedBankGraft_piece_cover
    (S : ClosedSeams E)
    (relation : ∀ x y, S.relation x y ↔ mappedBankGraftCells cells inner coordinates left right x y)
    (a : Total E) (finite : ∀ i, (classIn E S.relation a i).Finite) :
    ∃ ε > 0, ∀ r, 0 < r → r ≤ ε → ∀ b : Total X,
      edist (point X Banks (Restore a)) (point X Banks b) < ENNReal.ofReal r →
      ∃ c : X b.1, Relation.EqvGen Banks (Restore a) ⟨b.1, c⟩ ∧
        edist c b.2 < ENNReal.ofReal r := by
  obtain ⟨ε, positive, transport⟩ := S.class_transport a finite
  let A := (changeSeamsIsometryEquiv E
      (fun x y h => point_eq_of_glue E ((relation x y).mp h))
      (fun x y h => point_eq_of_glue E ((relation x y).mpr h))).trans
    (mappedBankGraftIsometry cells inner coordinates left right)
  have image {x y : Total E} (same : Relation.EqvGen S.relation x y) :
      Relation.EqvGen Banks (Restore x) (Restore y) := by
    induction same with
    | rel x y h =>
      exact mappedBankGraftCells_eqvGen_image cells inner coordinates left right
        x y ((relation x y).mp h)
    | refl x => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  refine ⟨ε, positive, ?_⟩
  intro r rpos small b near
  obtain ⟨z, rfl⟩ := mappedNestedPoint_surjective cells inner coordinates b
  have metric_near : edist (A (point E S.relation a)) (A (point E S.relation z)) <
      ENNReal.ofReal r := near
  rw [A.isometry.edist_eq] at metric_near
  obtain ⟨q, hq, close⟩ := exists_classPoint_of_edist_lt E S.relation a positive small
    finite transport z metric_near
  refine ⟨(Restore ⟨z.1, q⟩).2, image hq, ?_⟩
  have dist_near : edist q z.2 < ENNReal.ofReal r := by
    rw [edist_dist, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr close
  refine lt_of_le_of_lt ?_ dist_near
  let cell : J z.1.1 → Type _ := fun j => cells z.1.1 j
  let cut := inner z.1.1
  let F := coordinates z.1.1
  change edist (F (of cell cut z.1.2 q)) (F (of cell cut z.1.2 z.2)) ≤ edist q z.2
  exact (F.isometry.edist_eq _ _).trans_le (edist_of_le cell cut z.1.2 q z.2)

end Unfoldings.MetricGluing
