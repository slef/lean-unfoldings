module

public import Unfoldings.Convex.FiniteVisualHistoryCone
public import Unfoldings.FewestNets.FiniteProgressRouting100Witness
public import Unfoldings.FewestNets.FiniteProgressBodyExample

/-! Convert the first finite record's pair tests into a routing cone on each side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real MeshStar

theorem q100FirstBody_strict_side (side : Fin 6) :
    convexHull ℝ (Set.range q100FirstBody) ⊆
      {w | inner ℝ (q100FirstNormal side) w < q100FirstOffset side} := by
  have tested := checkQ100FirstSideWitness_pass side
  unfold checkQ100FirstSideWitness checkRoutingSide at tested
  simp only [Bool.and_eq_true] at tested
  exact progressBody_strictSide_of_check certificateDenominator_pos (checkedQ100FirstNormal side)
    checkQ100FirstBody (checkedQ100FirstOffset side) tested.1.1.1.1.1.1

/-- The first saved record supplies the required whole-side history aperture
and outward progress, with a finite exact interpretation of its visual tests. -/
theorem q100First_progressCone_on_side (side : Fin 6) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    let p := AffineMap.lineMap (q100FirstCorner (side - 1)) (q100FirstCorner side) t
    let L := convexHull ℝ (Set.range q100FirstBody)
    let θ := 81.841 * π / 180
    q100FirstOffset side ≤ inner ℝ (q100FirstNormal side) p →
      (∃ (axis : Plane) (width : ℝ), axis ≠ 0 ∧ θ < width ∧ width < π - θ ∧
        ∀ z : Plane, z ≠ 0 → (z ∈ SlopeEnvelope.historyCone L p ↔ angle axis z ≤ width / 2)) ∧
      ∀ z : Plane, z ∈ SlopeEnvelope.historyCone L p →
        0.0073243 * ‖z‖ ≤ inner ℝ z (q100FirstNormal side) := by
  dsimp only
  intro side_bound
  have angle_pos : 0 < 81.841 * π / 180 := by positivity
  have angle_small : 81.841 * π / 180 ≤ π / 2 := by linarith only [pi_pos]
  have h := routingCone_of_check certificateDenominator_pos
    (checkedQ100FirstCorner (side - 1)) (checkedQ100FirstCorner side)
    (checkedQ100FirstNormal side) checkQ100FirstBody
    q100FirstBody_cyclicConvex q100FirstCyclicBody_injective (checkedQ100FirstOffset side)
    checkQ100FirstCot checkQ100FirstGamma angle_pos angle_small (by norm_num)
    q100FirstCot_lt (by norm_num) (q100FirstNormal_unit side)
    (q100FirstSideWitness side) (checkQ100FirstSideWitness_pass side) ht side_bound
  refine ⟨h.1, ?_⟩
  intro z hz
  exact (h.2 z hz).trans_eq (real_inner_comm z (q100FirstNormal side))

end Unfoldings.FewestNets
