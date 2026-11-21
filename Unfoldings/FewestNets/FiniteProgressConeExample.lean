module

public import Unfoldings.Convex.FiniteVisualHistoryCone
public import Unfoldings.FewestNets.FiniteExteriorUnitNormal
public import Unfoldings.FewestNets.FiniteProgressBodyExample
public import Unfoldings.FewestNets.FiniteVisualUpperExample

/-! Convert the first finite record's pair tests into a routing cone on each side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real MeshStar

theorem q100FirstBody_strict_side (side : Fin 6) :
    convexHull ℝ (Set.range q100FirstBody) ⊆
      {w | inner ℝ (q100FirstNormal side) w < q100FirstOffset side} := by
  apply convexHull_min _ (convex_halfSpace_lt (innerSL ℝ (q100FirstNormal side)).toLinearMap.isLinear _)
  rintro _ ⟨i, rfl⟩
  change inner ℝ (q100FirstNormal side) (q100FirstBody i) < q100FirstOffset side
  by_contra! outside
  have lens (j k : Fin 48) (ordered : j < k) :
      0 < visualLensValue 0.1433718319 (q100FirstBody i) (q100FirstBody j) (q100FirstBody k) := by
    have h := q100FirstLenses_all side
    unfold checkQ100FirstLenses at h
    dsimp only at h
    have test := List.all_eq_true.mp (List.all_eq_true.mp h j (List.mem_finRange j))
      k (List.mem_finRange k)
    rw [ite_eq_left ordered] at test
    exact visualLensValue_pos_of_check certificateDenominator_pos (by norm_num)
      (q100FirstBody_injective.ne ordered.ne) checkQ100FirstCot (checkQ100FirstBody j)
      (checkQ100FirstBody k) (checkedQ100FirstNormal side) (checkedQ100FirstOffset side) outside
      test
  by_cases iz : i = 0
  · subst i
    have bad := lens 0 1 (by decide)
    simp [visualLensValue] at bad
  · have bad := lens 0 i (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm iz))
    simp [visualLensValue] at bad

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
  let p := AffineMap.lineMap (q100FirstCorner (side - 1)) (q100FirstCorner side) t
  have sight (i : Fin 48) : 0 < inner ℝ (q100FirstNormal side) (p - q100FirstBody i) := by
    have inside : q100FirstBody i ∈ convexHull ℝ (Set.range q100FirstBody) :=
      subset_convexHull ℝ _ ⟨i, rfl⟩
    have h := q100FirstBody_strict_side side inside
    change inner ℝ (q100FirstNormal side) (q100FirstBody i) < q100FirstOffset side at h
    rw [inner_sub_right]
    exact sub_pos.mpr (h.trans_le side_bound)
  have lo := lowerVisualAngle_q100_face_one_one (side - 1) ht
  dsimp only at lo
  rw [sub_add_cancel] at lo
  have hi (i j : Fin 48) (different : i ≠ j) :
      angle (p - q100FirstBody i) (p - q100FirstBody j) < π - 81.841 * π / 180 :=
    upperVisualAngle_q100_face_one_one side side_bound different
  constructor
  · obtain ⟨axis, width, nonzero, lower, higher, cone⟩ :=
      SlopeEnvelope.exists_historyCone_angle_of_vertex_bounds q100FirstBody p
        (q100FirstNormal side) sight (by positivity) (by linarith only [pi_pos]) lo hi
    exact ⟨axis, width, nonzero, by linarith only [lower], higher, cone⟩
  · intro z history
    rw [real_inner_comm]
    apply exteriorMargin_q100_face_one_one_checked side ht
    intro i
    have inside : q100FirstBody i ∈ convexHull ℝ (Set.range q100FirstBody) :=
      subset_convexHull ℝ _ ⟨i, rfl⟩
    rw [inner_sub_left, sub_nonneg]
    exact history (q100FirstBody i) inside

end Unfoldings.FewestNets
