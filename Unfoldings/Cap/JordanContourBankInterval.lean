module

public import Unfoldings.Cap.JordanContourBankOrder

/-! The actual geometric bank vertices form the strict interior of one cyclic contour interval. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- An arc's actual outgoing first bank determines its cyclic interval; both endpoint turns
are excluded exactly as required when comparing first and last link headings. -/
theorem jordanGeometricBankIndices_cyclic_interval {bank rest : Set Plane}
    (bank_closed : IsClosed bank) (rest_closed : IsClosed rest) (cover : J ⊆ bank ∪ rest)
    (first last : Fin ((K.jordanContour jordan contains avoids).length + 1))
    (contacts : bank ∩ rest ⊆ {K.jordanBankPosition jordan contains avoids first,
      K.jordanBankPosition jordan contains avoids last})
    (on_first : K.jordanContourBankOn jordan contains avoids bank first)
    (off_last : ¬ K.jordanContourBankOn jordan contains avoids bank last)
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    finCycle first i ∈ K.jordanGeometricBankIndices jordan contains avoids bank
        {K.jordanBankPosition jordan contains avoids first,
          K.jordanBankPosition jordan contains avoids last} ↔
      0 < i ∧ i < (finCycle first).symm last := by
  let pos := K.jordanBankPosition jordan contains avoids
  let cut := (finCycle first).symm last
  have zero : finCycle first 0 = first := by simp only [finCycle_apply, zero_add]
  have terminal : finCycle first cut = last := (finCycle first).apply_symm_apply last
  have at_first : pos (finCycle first i) = pos first ↔ i = 0 := by
    constructor
    · intro same
      exact (finCycle first).injective
        ((K.jordanBankPosition_injective jordan contains avoids same).trans zero.symm)
    · rintro rfl
      rw [zero]
  have at_last : pos (finCycle first i) = pos last ↔ i = cut := by
    constructor
    · intro same
      exact (finCycle first).injective
        ((K.jordanBankPosition_injective jordan contains avoids same).trans terminal.symm)
    · rintro rfl
      rw [terminal]
  have contacts_in_range : bank ∩ rest ⊆ Set.range pos := by
    intro x member
    rcases contacts member with same | same
    · exact ⟨first, same.symm⟩
    · exact ⟨last, (Set.mem_singleton_iff.mp same).symm⟩
  have runs := K.jordanContourBankOn_two_runs jordan contains avoids
    bank_closed rest_closed cover first last contacts i
  have outgoing : K.jordanContourBankOn jordan contains avoids bank (finCycle first i) ↔
      i < cut := by
    simpa [cut, on_first, off_last] using runs
  have marked : bank ∩ rest ⊆ ({pos first, pos last} : Finset Plane) := by
    intro x member
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    exact contacts member
  rw [K.jordanGeometricBankIndices_eq_bankOn jordan contains avoids
    bank_closed rest_closed cover contacts_in_range {pos first, pos last} marked]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, outgoing]
  change (i < cut ∧ ¬ (pos (finCycle first i) = pos first ∨
    pos (finCycle first i) = pos last)) ↔ _
  rw [at_first, at_last]
  constructor
  · rintro ⟨before, neither⟩
    exact ⟨lt_of_le_of_ne (Fin.zero_le _) (fun same => neither (Or.inl same.symm)), before⟩
  · rintro ⟨positive, before⟩
    exact ⟨before, fun same => same.elim positive.ne' before.ne⟩

include jordan contains avoids in
open Classical in
/-- Marked points outside the geometric bank cannot affect its actual turn sum. -/
theorem jordanGeometricBankIndices_congr_corners (bank : Set Plane)
    (corners other : Finset Plane) (same : ∀ z ∈ bank, z ∈ corners ↔ z ∈ other) :
    K.jordanGeometricBankIndices jordan contains avoids bank corners =
      K.jordanGeometricBankIndices jordan contains avoids bank other := by
  ext i
  simp only [jordanGeometricBankIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases member : K.jordanBankPosition jordan contains avoids i ∈ bank
  · rw [same _ member]
  · simp only [member, false_and]

end Unfoldings.ConvexCap
