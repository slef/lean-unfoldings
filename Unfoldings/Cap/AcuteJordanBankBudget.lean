module

public import Unfoldings.Cap.GeometricBankTurnComparison
public import Unfoldings.Cap.SharpCurvatureBudget
public import Unfoldings.Cap.SharpJordanClosingLink
public import Unfoldings.Geometry.AcuteChainClosure

/-! Integrate the sharp two-link closing bounds on a genuine acute-cone Jordan disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {n : ℕ} (P : PolygonalChain Plane n) (c : Plane)
  (jordan : Schoenflies.IsJordanCurve (P.twoLinkClosure c))
  (contains : P.twoLinkClosure c ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) (P.twoLinkClosure c))

include jordan contains avoids in
open Classical in
/-- Two transverse links and three single-face corner estimates bound the turn of
the bank facing this disk, with one allowance for the enclosed curvature. -/
theorem abs_acute_bank_turn_error_le_of_regular_links
    (inside : P.twoLinkClosure c ⊆ interior K.footprint)
    (h k : Plane →L[ℝ] ℝ) (nonempty : 0 < n)
    (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))
    (initial : h c ≤ h (P.vertex 0)) (terminal : k (P.vertex (Fin.last n)) ≤ k c)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    let Q := K.jordanContour jordan contains avoids
    let pos := K.jordanBankPosition jordan contains avoids
    let err := K.jordanContourTurnError jordan contains avoids
    let bank := Set.range P.path
    let corners := P.twoClosingCorners c
    let links := P.twoClosingLinks c
    (∀ i : Fin (Q.length + 1), pos i ∈ corners → |err i| ≤ 2 * arcsin (tan (φ / 2) ^ 2)) →
    (∀ (j : Fin 2) (i : Fin (Q.length + 1)),
      pos i ∈ segment ℝ (links j).1 (links j).2 → pos i ∉ bank → pos i ∉ corners →
      K.HasRegularSectionSlopes ((K.jordanContourVertexEquiv jordan contains avoids) i).val
        ((links j).2 - (links j).1)) →
    |∑ i ∈ K.jordanGeometricBankIndices jordan contains avoids bank corners, err i| ≤
      acuteConeDevelopmentHeading φ := by
  classical
  dsimp only
  intro at_corner regular
  let Q := K.jordanContour jordan contains avoids
  let pos := K.jordanBankPosition jordan contains avoids
  let err := K.jordanContourTurnError jordan contains avoids
  let I := Fin (Q.length + 1)
  let weight (i : I) := |err i|
  let corner := P.twoClosingCorners c
  let bank := Set.range P.path
  let links := P.twoClosingLinks c
  let arc (j : Fin 2) := segment ℝ (links j).1 (links j).2
  let selected := K.jordanGeometricBankIndices jordan contains avoids bank corner
  let corners := Finset.univ.filter (fun i : I => pos i ∈ corner)
  let sections (j : Fin 2) := Finset.univ.filter (fun i : I =>
    pos i ∈ arc j ∧ pos i ∉ bank ∧ pos i ∉ corner)
  let Δ := 2 * arcsin (tan (φ / 2) ^ 2)
  have delta_nonneg : 0 ≤ Δ := mul_nonneg (by norm_num)
    (by rw [← arcsin_zero]; exact arcsin_le_arcsin (sq_nonneg _))
  have cover : P.twoLinkClosure c ⊆ bank ∪ ⋃ j, arc j := by
    rintro x (on_bank | on_final | on_initial)
    · exact Or.inl on_bank
    · exact Or.inr (Set.mem_iUnion.mpr ⟨0, on_final⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨1, on_initial⟩)
  have corner_card : corner.card ≤ 3 := by
    classical
    change ({P.vertex 0, P.vertex (Fin.last n), c} : Finset Plane).card ≤ 3
    have a := Finset.card_insert_le (P.vertex 0) ({P.vertex (Fin.last n), c} : Finset Plane)
    have b := Finset.card_insert_le (P.vertex (Fin.last n)) ({c} : Finset Plane)
    rw [Finset.card_singleton] at b
    omega
  have corner_sum : (∑ i ∈ corners, weight i) ≤ 3 * Δ := by
    have each (i : I) (member : i ∈ corners) : weight i ≤ Δ :=
      at_corner i (Finset.mem_filter.mp member).2
    have total := Finset.sum_le_card_nsmul corners weight Δ each
    have bound := (K.card_jordanBankPosition_preimage_le jordan contains avoids corner).trans
      corner_card
    rw [nsmul_eq_mul] at total
    exact total.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast bound) delta_nonneg)
  have different (j : Fin 2) : (links j).1 ≠ (links j).2 := by
    have ends : (0 : Fin (n + 1)) < Fin.last n := nonempty
    have h_lt := P.strictMono_linear_vertices h first ends
    have k_lt := P.strictMono_linear_vertices k last ends
    change h (P.vertex 0) < h (P.vertex (Fin.last n)) at h_lt
    change k (P.vertex 0) < k (P.vertex (Fin.last n)) at k_lt
    fin_cases j
    · intro equal
      change P.vertex (Fin.last n) = c at equal
      exact h_lt.not_ge (equal.symm ▸ initial)
    · intro equal
      change c = P.vertex 0 at equal
      exact k_lt.not_ge (equal ▸ terminal)
  have contacts (j l : Fin 2) (different : j ≠ l) :
      arc j ∩ arc l ⊆ (corner : Set Plane) := by
    have at_apex := P.twoClosingLinks_inter_subset c h k first last initial terminal nonempty
    have apex : ({c} : Set Plane) ⊆ (corner : Set Plane) := by
      rw [Set.singleton_subset_iff]
      simp [corner, PolygonalChain.twoClosingCorners]
    fin_cases j <;> fin_cases l
    · exact (different rfl).elim
    · exact at_apex.trans apex
    · exact (Set.inter_comm _ _) ▸ at_apex.trans apex
    · exact (different rfl).elim
  have section_bound (j : Fin 2) : (∑ i ∈ sections j, weight i) ≤ 2 * φ * sin φ := by
    let remainder := bank ∪ ⋃ l : {l // l ≠ j}, arc l.val
    have closed : IsClosed remainder := (isCompact_range P.path.continuous).isClosed.union
      (isClosed_iUnion_of_finite (fun l => (compact_segment (links l.val).1 (links l.val).2).isClosed))
    have curve_cover : P.twoLinkClosure c ⊆ arc j ∪ remainder := by
      intro x member
      rcases cover member with on_bank | on_link
      · exact Or.inr (Or.inl on_bank)
      · obtain ⟨l, on_l⟩ := Set.mem_iUnion.mp on_link
        by_cases same : l = j
        · exact Or.inl (same ▸ on_l)
        · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨l, same⟩, on_l⟩))
    apply K.sum_abs_jordan_closing_link_error_le_sin_tilt jordan contains avoids inside
      (sections j) (links j).1 (links j).2 (different j) remainder closed curve_cover _ _
      nonnegative small tilt
    · intro i member
      obtain ⟨on_link, off_bank, off_corner⟩ := (Finset.mem_filter.mp member).2
      rintro (on_bank | on_other)
      · exact off_bank on_bank
      · obtain ⟨l, on_l⟩ := Set.mem_iUnion.mp on_other
        exact off_corner (contacts j l.val l.property.symm ⟨on_link, on_l⟩)
    · intro i member
      obtain ⟨on_link, off_bank, off_corner⟩ := (Finset.mem_filter.mp member).2
      exact regular j i on_link off_bank off_corner
  let pieces : Fin 3 → Finset I := Fin.cons corners sections
  have covered (i : I) (member : i ∈ selectedᶜ) : ∃ j, i ∈ pieces j := by
    by_cases is_corner : pos i ∈ corner
    · exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ i, is_corner⟩⟩
    · have off_bank : pos i ∉ bank := fun on_bank =>
        (Finset.mem_compl.mp member) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, on_bank, is_corner⟩)
      obtain ⟨j, on_link⟩ := Set.mem_iUnion.mp ((cover
        (K.jordanBankPosition_mem_curve jordan contains avoids i)).resolve_left off_bank)
      exact ⟨j.succ, by
        simp only [pieces, Fin.cons_succ]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, on_link, off_bank, is_corner⟩⟩
  have absolute := sum_le_sum_of_finite_cover selectedᶜ pieces weight (fun _ => abs_nonneg _) covered
  rw [Fin.sum_univ_succ] at absolute
  simp only [pieces, Fin.cons_zero, Fin.cons_succ] at absolute
  have links_bound : (∑ j : Fin 2, ∑ i ∈ sections j, weight i) ≤ 4 * φ * sin φ := by
    rw [Fin.sum_univ_two]
    linarith only [section_bound 0, section_bound 1]
  have estimate := K.abs_jordan_bank_turn_error_le jordan contains avoids inside selected
    ((Finset.abs_sum_le_sum_abs _ _).trans (absolute.trans (add_le_add corner_sum links_bound)))
  have curvature := K.totalCurvature_le_shallowDevelopmentCurvature nonnegative small tilt
  unfold acuteConeDevelopmentHeading
  linarith only [estimate, curvature]

end Unfoldings.ConvexCap
