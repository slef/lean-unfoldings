module

public import Unfoldings.FewestNets.FiniteVisualSideBounds
public import Unfoldings.FewestNets.CheckedVisualLens

/-! Kernel checks of the progress-body pair lenses for the first finite record. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real MeshStar
local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Validate every pair's strict lens support on this supporting line. -/
def checkQ100FirstLenses (side : Fin 6) : Bool :=
  let normal := checkedQ100FirstNormal side
  let offset := checkedQ100FirstOffset side
  (List.finRange 48).all fun i => (List.finRange 48).all fun j =>
    if i < j then checkLensSupport certificateDenominator_pos checkQ100FirstCot
      (checkQ100FirstBody i) (checkQ100FirstBody j) normal offset else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
-- The kernel scans all unordered pairs on each of the six supporting lines.
theorem q100FirstLenses_all (side : Fin 6) : checkQ100FirstLenses side = true := by
  fin_cases side <;> decide +kernel

/-- The first supporting line passes the complete pair scan. -/
theorem q100FirstLenses_side_zero : checkQ100FirstLenses 0 = true := q100FirstLenses_all 0

set_option maxRecDepth 8192 in
/-- The rational coordinate list consists of distinct vertices. -/
theorem q100FirstBodyCoordinates_injective : Function.Injective q100FirstBodyCoordinates := by
  unfold Function.Injective
  decide +kernel

theorem q100FirstBody_injective : Function.Injective q100FirstBody := by
  intro i j eq
  apply q100FirstBodyCoordinates_injective
  apply Prod.ext
  · have h := congrArg (fun p : Plane => p 0) eq
    change ((q100FirstBodyCoordinates i).1 : ℝ) = (q100FirstBodyCoordinates j).1 at h
    exact_mod_cast h
  · have h := congrArg (fun p : Plane => p 1) eq
    change ((q100FirstBodyCoordinates i).2 : ℝ) = (q100FirstBodyCoordinates j).2 at h
    exact_mod_cast h

/-- On each supporting line and beyond, all distinct body pairs satisfy
the strict upper visual-angle bound. -/
theorem upperVisualAngle_q100_face_one_one (side : Fin 6) {p : Plane}
    (hp : q100FirstOffset side ≤ inner ℝ (q100FirstNormal side) p)
    {i j : Fin 48} (different : i ≠ j) :
    angle (p - q100FirstBody i) (p - q100FirstBody j) < π - 81.841 * π / 180 := by
  wlog ordered : i < j generalizing i j
  · rw [angle_comm]
    exact this different.symm (lt_of_le_of_ne (le_of_not_gt ordered) different.symm)
  have h := q100FirstLenses_all side
  unfold checkQ100FirstLenses at h
  dsimp only at h
  have test := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i))
    j (List.mem_finRange j)
  rw [ite_eq_left ordered] at test
  have outside := visualLensValue_pos_of_check certificateDenominator_pos (by norm_num)
    (q100FirstBody_injective.ne different) checkQ100FirstCot (checkQ100FirstBody i)
    (checkQ100FirstBody j) (checkedQ100FirstNormal side) (checkedQ100FirstOffset side) hp test
  exact visualAngle_lt_supplement_of_outside_lens certificateOrientation
    (by positivity) (by linarith [pi_pos]) (by norm_num) q100FirstCot_lt outside

/-- On the first supporting line and beyond, all distinct body pairs satisfy
the strict upper visual-angle bound. -/
theorem upperVisualAngle_q100_face_one_one_side_zero {p : Plane}
    (hp : q100FirstOffset 0 ≤ inner ℝ (q100FirstNormal 0) p) {i j : Fin 48} (different : i ≠ j) :
    angle (p - q100FirstBody i) (p - q100FirstBody j) < π - 81.841 * π / 180 :=
  upperVisualAngle_q100_face_one_one 0 hp different

end Unfoldings.FewestNets
