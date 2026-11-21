module

public import Unfoldings.Cap.RadialBankTurnComparison
public import Unfoldings.Cap.SharpCurvatureBudget
public import Unfoldings.Cap.SharpRelativeAngleProjection

/-! The sharp bounds for the actual corners and links combine in the radial bank budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {n : ℕ} (P : PolygonalChain Plane n) (q c : Plane)
  (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure q c))
  (contains : P.threeSegmentClosure q c ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) (P.threeSegmentClosure q c))

include jordan contains avoids in
open Classical in
/-- The one-sided estimate uses exactly one curvature allowance. The corner at the
source is controlled by relative projection error, and each other corner and open
closing link contributes its own local bound. -/
theorem abs_radial_bank_turn_error_le_sharp_of_local_bounds
    (inside : P.threeSegmentClosure q c ⊆ interior K.footprint)
    {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) :
    let a := P.vertex 0
    let b := P.vertex (Fin.last n)
    let Q := K.jordanContour jordan contains avoids
    let pos := K.jordanBankPosition jordan contains avoids
    let err := K.jordanContourTurnError jordan contains avoids
    let bank := Set.range P.path
    let corners := radialClosingCorners q a b c
    let links := radialClosingLinks q a b c
    (∀ i : Fin (Q.length + 1), pos i = a ∨ pos i = b ∨ pos i = c →
      |err i| ≤ 2 * arcsin (tan (φ / 2) ^ 2)) →
    (∀ k : Fin 3,
      (∑ i ∈ Finset.univ.filter (fun i => pos i ∈ segment ℝ (links k).1 (links k).2 ∧
        pos i ∉ bank ∧ pos i ∉ corners), |err i|) ≤ 2 * φ * sin φ) →
    |∑ i ∈ K.jordanGeometricBankIndices jordan contains avoids bank corners, err i| ≤
      shallowDevelopmentHeading φ - shallowDevelopmentCurvature φ := by
  classical
  dsimp only
  intro endpoints sections
  let Q := K.jordanContour jordan contains avoids
  let pos := K.jordanBankPosition jordan contains avoids
  let err := K.jordanContourTurnError jordan contains avoids
  let a := P.vertex 0
  let b := P.vertex (Fin.last n)
  let bank := Set.range P.path
  let corners := radialClosingCorners q a b c
  let links := radialClosingLinks q a b c
  let I := Fin (Q.length + 1)
  let weight (i : I) := |err i|
  let ε := (cos φ)⁻¹ - 1
  let Δ := 2 * arcsin (tan (φ / 2) ^ 2)
  let named : Fin 4 → Plane := ![q, a, b, c]
  let budget : Fin 4 → ℝ := ![ε * (2 * π), Δ, Δ, Δ]
  let selected := K.jordanGeometricBankIndices jordan contains avoids bank corners
  let atCorner (k : Fin 4) := Finset.univ.filter (fun i : I => pos i = named k)
  let onLink (k : Fin 3) := Finset.univ.filter (fun i : I =>
    pos i ∈ segment ℝ (links k).1 (links k).2 ∧ pos i ∉ bank ∧ pos i ∉ corners)
  have cp : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith only [nonnegative, pi_pos], small⟩
  have ε_nonneg : 0 ≤ ε := sub_nonneg.mpr ((one_le_inv₀ cp).mpr (cos_le_one _))
  have Δ_nonneg : 0 ≤ Δ := mul_nonneg (by norm_num)
    (by rw [← arcsin_zero]; exact arcsin_le_arcsin (sq_nonneg _))
  have budget_nonneg (k : Fin 4) : 0 ≤ budget k := by
    fin_cases k <;> first | exact mul_nonneg ε_nonneg (by positivity) | exact Δ_nonneg
  have corner_error (k : Fin 4) (i : I) (member : i ∈ atCorner k) : weight i ≤ budget k := by
    have same := (Finset.mem_filter.mp member).2
    fin_cases k
    · exact K.abs_jordan_corner_error_le jordan contains avoids inside ε_nonneg
        (K.relativeCornerAngleError_sec_tilt nonnegative small tilt) i
    · exact endpoints i (Or.inl same)
    · exact endpoints i (Or.inr (Or.inl same))
    · exact endpoints i (Or.inr (Or.inr same))
  have corner_card (k : Fin 4) : (atCorner k).card ≤ 1 := by
    simpa only [atCorner, Finset.mem_singleton, Finset.card_singleton] using
      K.card_jordanBankPosition_preimage_le jordan contains avoids {named k}
  have corner_sum (k : Fin 4) : (∑ i ∈ atCorner k, weight i) ≤ budget k := by
    have total := Finset.sum_le_card_nsmul (atCorner k) weight (budget k) (corner_error k)
    rw [nsmul_eq_mul] at total
    have card : ((atCorner k).card : ℝ) ≤ 1 := by exact_mod_cast corner_card k
    exact total.trans ((mul_le_mul_of_nonneg_right card (budget_nonneg k)).trans_eq (one_mul _))
  let pieces : Fin 4 ⊕ Fin 3 → Finset I := Sum.elim atCorner onLink
  have covered (i : I) (outside : i ∈ selectedᶜ) : ∃ k, i ∈ pieces k := by
    by_cases corner : pos i ∈ corners
    · have named_corner : pos i = a ∨ pos i = b ∨ pos i = q ∨ pos i = c := by
        simpa only [corners, radialClosingCorners, Finset.mem_insert, Finset.mem_singleton]
          using corner
      rcases named_corner with ha | hb | hq | hc
      · exact ⟨.inl 1, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ha⟩⟩
      · exact ⟨.inl 2, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hb⟩⟩
      · exact ⟨.inl 0, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hq⟩⟩
      · exact ⟨.inl 3, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩⟩
    · have off_bank : pos i ∉ bank := by
        intro bank_mem
        exact (Finset.mem_compl.mp outside) (Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, bank_mem, corner⟩)
      rcases (K.jordanBankPosition_mem_curve jordan contains avoids i) with
        bank_mem | ((terminal | middle) | initial)
      · exact (off_bank bank_mem).elim
      · exact ⟨.inr 0, Finset.mem_filter.mpr ⟨Finset.mem_univ i, terminal, off_bank, corner⟩⟩
      · exact ⟨.inr 1, Finset.mem_filter.mpr ⟨Finset.mem_univ i, middle, off_bank, corner⟩⟩
      · exact ⟨.inr 2, Finset.mem_filter.mpr ⟨Finset.mem_univ i, initial, off_bank, corner⟩⟩
  have estimates := sum_le_sum_of_finite_cover selectedᶜ pieces weight
    (fun _ => abs_nonneg _) covered
  rw [Fintype.sum_sum_type] at estimates
  change (∑ i ∈ selectedᶜ, weight i) ≤
    (∑ k : Fin 4, ∑ i ∈ atCorner k, weight i) + ∑ k : Fin 3, ∑ i ∈ onLink k, weight i at estimates
  have corner_total : (∑ k : Fin 4, ∑ i ∈ atCorner k, weight i) ≤ ε * (2 * π) + 3 * Δ :=
    (Finset.sum_le_sum (fun k _ => corner_sum k)).trans_eq (by
      rw [Fin.sum_univ_four]
      change ε * (2 * π) + Δ + Δ + Δ = ε * (2 * π) + 3 * Δ
      ring)
  have link_total : (∑ k : Fin 3, ∑ i ∈ onLink k, weight i) ≤ 6 * φ * sin φ :=
    (Finset.sum_le_sum (fun k _ => sections k)).trans_eq (by
      rw [Fin.sum_univ_three]
      ring)
  have bound := K.abs_jordan_bank_turn_error_le jordan contains avoids inside selected
    ((Finset.abs_sum_le_sum_abs _ _).trans (estimates.trans (add_le_add corner_total link_total)))
  have curvature := K.totalCurvature_le_shallowDevelopmentCurvature nonnegative small tilt
  dsimp only [shallowDevelopmentHeading, Δ, ε]
  linarith only [bound, curvature]

end Unfoldings.ConvexCap
