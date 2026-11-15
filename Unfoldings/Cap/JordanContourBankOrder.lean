module

public import Unfoldings.Cap.JordanContourPartition
public import Unfoldings.Cap.GeometricBankTurnComparison
public import Unfoldings.Topology.FiniteTwoCutOrder

/-! Geometric arc membership determines the actual bank labels and their allowed transitions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- The whole outgoing physical contour bank belongs to this geometric arc. -/
def jordanContourBankOn (bank : Set Plane)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) : Prop :=
  segment ℝ (K.jordanBankPosition jordan contains avoids i)
    (K.jordanBankPosition jordan contains avoids
      (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) ⊆ bank

include jordan contains avoids in
open Classical in
/-- Away from common contacts, point membership determines the actual outgoing bank. -/
theorem jordanContourBankOn_iff_of_not_contact {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (contacts : bank ∩ rest ⊆ Set.range (K.jordanBankPosition jordan contains avoids))
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (regular : K.jordanBankPosition jordan contains avoids i ∉ bank ∩ rest) :
    K.jordanContourBankOn jordan contains avoids bank i ↔
      K.jordanBankPosition jordan contains avoids i ∈ bank := by
  constructor
  · intro whole
    exact whole (left_mem_segment ℝ _ _)
  · intro member
    rcases K.jordanContour_segment_subset_left_or_right jordan contains avoids
      bank_closed rest_closed cover contacts i with whole | other
    · exact whole
    · exact (regular ⟨member, other (left_mem_segment ℝ _ _)⟩).elim

include jordan contains avoids in
open Classical in
/-- Consecutive actual banks can switch arcs only at a common geometric contact. -/
theorem jordanContourBankOn_step_iff_of_not_contact {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (contacts : bank ∩ rest ⊆ Set.range (K.jordanBankPosition jordan contains avoids))
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (regular : K.jordanBankPosition jordan contains avoids
      (finRotate ((K.jordanContour jordan contains avoids).length + 1) i) ∉ bank ∩ rest) :
    K.jordanContourBankOn jordan contains avoids bank i ↔
      K.jordanContourBankOn jordan contains avoids bank
        (finRotate ((K.jordanContour jordan contains avoids).length + 1) i) := by
  rw [K.jordanContourBankOn_iff_of_not_contact jordan contains avoids
    bank_closed rest_closed cover contacts _ regular]
  constructor
  · intro whole
    exact whole (right_mem_segment ℝ _ _)
  · intro member
    rcases K.jordanContour_segment_subset_left_or_right jordan contains avoids
      bank_closed rest_closed cover contacts i with whole | other
    · exact whole
    · exact (regular ⟨member, other (right_mem_segment ℝ _ _)⟩).elim

include jordan contains avoids in
open Classical in
/-- The geometric bank sum uses precisely the actual outgoing banks, with corners removed. -/
theorem jordanGeometricBankIndices_eq_bankOn {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (contacts : bank ∩ rest ⊆ Set.range (K.jordanBankPosition jordan contains avoids))
    (corners : Finset Plane) (marked : bank ∩ rest ⊆ (corners : Set Plane)) :
    K.jordanGeometricBankIndices jordan contains avoids bank corners =
      Finset.univ.filter (fun i => K.jordanContourBankOn jordan contains avoids bank i ∧
        K.jordanBankPosition jordan contains avoids i ∉ corners) := by
  ext i
  simp only [jordanGeometricBankIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases corner : K.jordanBankPosition jordan contains avoids i ∈ corners
  · simp only [corner, not_true_eq_false, and_false]
  · have regular : K.jordanBankPosition jordan contains avoids i ∉ bank ∩ rest :=
      fun member => corner (marked member)
    rw [K.jordanContourBankOn_iff_of_not_contact jordan contains avoids
      bank_closed rest_closed cover contacts i regular]

include jordan contains avoids in
open Classical in
/-- Two geometric contacts force two cyclic bank runs, starting at the first contact. -/
theorem jordanContourBankOn_two_runs {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (first last : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (contacts : bank ∩ rest ⊆ {K.jordanBankPosition jordan contains avoids first,
      K.jordanBankPosition jordan contains avoids last})
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    K.jordanContourBankOn jordan contains avoids bank (finCycle first i) ↔
      if i < (finCycle first).symm last then
        K.jordanContourBankOn jordan contains avoids bank first
      else K.jordanContourBankOn jordan contains avoids bank last := by
  let Q := K.jordanContour jordan contains avoids
  let pos := K.jordanBankPosition jordan contains avoids
  let cut := (finCycle first).symm last
  let label (j : Fin (Q.length + 1)) :=
    K.jordanContourBankOn jordan contains avoids bank (finCycle first j)
  have contacts_in_range : bank ∩ rest ⊆ Set.range pos := by
    intro x member
    rcases contacts member with same | same
    · exact ⟨first, same.symm⟩
    · exact ⟨last, (Set.mem_singleton_iff.mp same).symm⟩
  have steps (j : Fin Q.length) (different : j.succ ≠ cut) :
      label j.succ = label j.castSucc := by
    have next : finRotate (Q.length + 1) (finCycle first j.castSucc) =
        finCycle first j.succ := by
      simp only [finRotate_apply, finCycle_apply]
      rw [← Fin.coeSucc_eq_succ]
      abel
    have regular : pos (finCycle first j.succ) ∉ bank ∩ rest := by
      intro member
      have marked := contacts member
      rcases marked with same | same
      · have index := K.jordanBankPosition_injective jordan contains avoids same
        have zero : finCycle first 0 = first := by simp only [finCycle_apply, zero_add]
        have impossible := (finCycle first).injective (index.trans zero.symm)
        exact Fin.succ_ne_zero j impossible
      · apply different
        exact (finCycle first).injective
          ((K.jordanBankPosition_injective jordan contains avoids
            (Set.mem_singleton_iff.mp same)).trans ((finCycle first).apply_symm_apply last).symm)
    have same := K.jordanContourBankOn_step_iff_of_not_contact jordan contains avoids
      bank_closed rest_closed cover contacts_in_range (finCycle first j.castSucc)
      (next ▸ regular)
    rw [next] at same
    exact propext same.symm
  have runs := fin_two_runs_of_steps label cut steps i
  have zero : finCycle first 0 = first := by simp only [finCycle_apply, zero_add]
  have terminal : finCycle first cut = last := (finCycle first).apply_symm_apply last
  change label i ↔ _
  rw [runs]
  simp only [label, zero, terminal]
  rfl

include jordan contains avoids in
open Classical in
/-- Two nontrivial geometric arcs occupy opposite actual contour runs. -/
theorem jordanContourBankOn_contacts_complementary {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (first last : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (contacts : bank ∩ rest ⊆ {K.jordanBankPosition jordan contains avoids first,
      K.jordanBankPosition jordan contains avoids last})
    (bank_witness : ∃ x ∈ J, x ∉ rest) (rest_witness : ∃ x ∈ J, x ∉ bank) :
    K.jordanContourBankOn jordan contains avoids bank first ↔
      ¬ K.jordanContourBankOn jordan contains avoids bank last := by
  let pos := K.jordanBankPosition jordan contains avoids
  have contacts_in_range : bank ∩ rest ⊆ Set.range pos := by
    intro x member
    rcases contacts member with same | same
    · exact ⟨first, same.symm⟩
    · exact ⟨last, (Set.mem_singleton_iff.mp same).symm⟩
  obtain ⟨x, x_curve, x_outside⟩ := bank_witness
  rw [K.jordanCurve_eq_contour_segments jordan contains avoids] at x_curve
  obtain ⟨a, on_a⟩ := Set.mem_iUnion.mp x_curve
  have bank_a : K.jordanContourBankOn jordan contains avoids bank a := by
    rcases K.jordanContour_segment_subset_left_or_right jordan contains avoids
      bank_closed rest_closed cover contacts_in_range a with whole | other
    · exact whole
    · exact (x_outside (other on_a)).elim
  obtain ⟨y, y_curve, y_outside⟩ := rest_witness
  rw [K.jordanCurve_eq_contour_segments jordan contains avoids] at y_curve
  obtain ⟨b, on_b⟩ := Set.mem_iUnion.mp y_curve
  have bank_b : ¬ K.jordanContourBankOn jordan contains avoids bank b :=
    fun whole => y_outside (whole on_b)
  have inconsistent (same : K.jordanContourBankOn jordan contains avoids bank first ↔
      K.jordanContourBankOn jordan contains avoids bank last) : False := by
    have constant (j) : K.jordanContourBankOn jordan contains avoids bank j ↔
        K.jordanContourBankOn jordan contains avoids bank first := by
      have runs := K.jordanContourBankOn_two_runs jordan contains avoids
        bank_closed rest_closed cover first last contacts ((finCycle first).symm j)
      rw [(finCycle first).apply_symm_apply] at runs
      apply runs.trans
      split_ifs
      · rfl
      · exact same.symm
    exact bank_b ((constant b).mpr ((constant a).mp bank_a))
  constructor
  · intro at_first at_last
    exact inconsistent ⟨fun _ => at_last, fun _ => at_first⟩
  · intro not_last
    by_contra not_first
    exact inconsistent ⟨fun h => (not_first h).elim, fun h => (not_last h).elim⟩

end Unfoldings.ConvexCap
