module

public import Unfoldings.Cap.JordanClosingLink
public import Unfoldings.Cap.JordanCornerError
public import Unfoldings.Cap.JordanBankPositions
public import Unfoldings.Topology.FiniteWeightedCover
public import Unfoldings.Geometry.SegmentVertices

/-!
# Bank comparison from an actual finite segment closure

Closing links and their intersections are literal geometric sets. Their turn
bounds are proved from straightness and the original cap faces. No assumed
closing-turn budget, traversal order, or development of the curved filling occurs.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- Actual bank vertices, excluding the finitely many geometric closing corners. -/
def jordanGeometricBankIndices (bank : Set Plane) (corners : Finset Plane) :
    Finset (Fin ((K.jordanContour jordan contains avoids).length + 1)) :=
  Finset.univ.filter (fun i => K.jordanBankPosition jordan contains avoids i ∈ bank ∧
    K.jordanBankPosition jordan contains avoids i ∉ corners)

include jordan contains avoids in
open Classical in
/-- Every actual straight closing link and geometric corner is charged once in a uniform bound. -/
theorem abs_jordan_geometric_bank_error_le (inside : J ⊆ interior K.footprint)
    (bank : Set Plane) (bank_closed : IsClosed bank) {m : ℕ} (links : Fin m → Plane × Plane)
    (different : ∀ k, (links k).1 ≠ (links k).2) (corners : Finset Plane)
    (cover : J ⊆ bank ∪ ⋃ k, segment ℝ (links k).1 (links k).2)
    (contacts : ∀ k j, k ≠ j → segment ℝ (links k).1 (links k).2 ∩
      segment ℝ (links j).1 (links j).2 ⊆ (corners : Set Plane))
    {ε φ : ℝ} (error_nonnegative : 0 ≤ ε) (error : K.RelativeCornerAngleError ε)
    (nonnegative : 0 ≤ φ) (small : φ < Real.pi / 2) (tilt : K.TiltBound φ) :
    |∑ i ∈ K.jordanGeometricBankIndices jordan contains avoids bank corners,
      K.jordanContourTurnError jordan contains avoids i| ≤
      C.totalInteriorAngularDefect Set.univ +
        (2 * (m : ℝ) * φ + (corners.card : ℝ) * (ε * (2 * Real.pi))) := by
  classical
  let Q := K.jordanContour jordan contains avoids
  let pos := K.jordanBankPosition jordan contains avoids
  let weight (i : Fin (Q.length + 1)) := |K.jordanContourTurnError jordan contains avoids i|
  let selected := K.jordanGeometricBankIndices jordan contains avoids bank corners
  let corner_indices := Finset.univ.filter (fun i => pos i ∈ corners)
  let section_indices (k : Fin m) := Finset.univ.filter (fun i =>
    pos i ∈ segment ℝ (links k).1 (links k).2 ∧ pos i ∉ bank ∧ pos i ∉ corners)
  have sections (k : Fin m) : (∑ i ∈ section_indices k, weight i) ≤ 2 * φ := by
    let remainder := bank ∪ ⋃ j : {j : Fin m // j ≠ k}, segment ℝ (links j.val).1 (links j.val).2
    have closed : IsClosed remainder := bank_closed.union
      (isClosed_iUnion_of_finite (fun j =>
        (compact_segment (links j.val).1 (links j.val).2).isClosed))
    have curve_cover : J ⊆ segment ℝ (links k).1 (links k).2 ∪ remainder := by
      intro x on_curve
      rcases cover on_curve with on_bank | on_link
      · exact Or.inr (Or.inl on_bank)
      · obtain ⟨j, member⟩ := Set.mem_iUnion.mp on_link
        by_cases same : j = k
        · exact Or.inl (same ▸ member)
        · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨j, same⟩, member⟩))
    have outside (i) (member : i ∈ section_indices k) : pos i ∉ remainder := by
      obtain ⟨on_link, off_bank, off_corner⟩ := (Finset.mem_filter.mp member).2
      rintro (on_bank | on_other)
      · exact off_bank on_bank
      · obtain ⟨j, other_member⟩ := Set.mem_iUnion.mp on_other
        exact off_corner (contacts k j.val j.property.symm ⟨on_link, other_member⟩)
    exact K.sum_abs_jordan_closing_link_error_le_tilt jordan contains avoids inside
      (section_indices k) (links k).1 (links k).2 (different k) remainder closed curve_cover outside
      nonnegative small tilt
  have delta_nonnegative : 0 ≤ ε * (2 * Real.pi) := mul_nonneg error_nonnegative (by positivity)
  have corner_sum : (∑ i ∈ corner_indices, weight i) ≤
      (corners.card : ℝ) * (ε * (2 * Real.pi)) := by
    have each (i) (_member : i ∈ corner_indices) : weight i ≤ ε * (2 * Real.pi) :=
      K.abs_jordan_corner_error_le jordan contains avoids inside error_nonnegative error i
    have sum_bound := Finset.sum_le_card_nsmul corner_indices weight (ε * (2 * Real.pi)) each
    have card_bound := K.card_jordanBankPosition_preimage_le jordan contains avoids corners
    exact sum_bound.trans (by
      simpa only [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr card_bound) delta_nonnegative)
  let pieces : Fin (m + 1) → Finset (Fin (Q.length + 1)) := Fin.cons corner_indices section_indices
  have covered (i) (member : i ∈ selectedᶜ) : ∃ a, i ∈ pieces a := by
    by_cases corner : pos i ∈ corners
    · exact ⟨0, by simpa only [pieces, Fin.cons_zero] using
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, corner⟩ : i ∈ corner_indices)⟩
    · have off_bank : pos i ∉ bank := by
        intro present
        apply Finset.mem_compl.mp member
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, present, corner⟩
      have on_curve := K.jordanBankPosition_mem_curve jordan contains avoids i
      obtain ⟨k, on_link⟩ := Set.mem_iUnion.mp ((cover on_curve).resolve_left off_bank)
      exact ⟨k.succ, by simpa only [pieces, Fin.cons_succ] using
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, on_link, off_bank, corner⟩ :
          i ∈ section_indices k)⟩
  have cover_bound := sum_le_sum_of_finite_cover selectedᶜ pieces weight
    (fun i => abs_nonneg _) covered
  rw [Fin.sum_univ_succ] at cover_bound
  simp only [pieces, Fin.cons_zero, Fin.cons_succ] at cover_bound
  have section_sum : (∑ k : Fin m, ∑ i ∈ section_indices k, weight i) ≤ 2 * (m : ℝ) * φ := by
    have bound := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) => sections k)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at bound
    exact bound.trans_eq (by ring)
  apply K.abs_jordan_bank_turn_error_le jordan contains avoids inside selected
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (cover_bound.trans (by linarith [corner_sum, section_sum]))

end Unfoldings.ConvexCap
