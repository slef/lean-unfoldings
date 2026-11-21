module

public import Unfoldings.FewestNets.FiniteVisualExample
public import Unfoldings.FewestNets.CheckedVisualLens

/-! Kernel checks of the progress-body pair lenses for the first finite record. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real MeshStar
local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

def q100FirstNormal (i : Fin 6) : Plane := (face 100 1 1).physicalSideNormal i

def q100FirstOffset (i : Fin 6) : ℝ := (face 100 1 1).derivativeNormalizedSideOffset 100 i

def checkQ100FirstNormal (i : Fin 6) : CheckedPlane certificateDenominator (q100FirstNormal i) :=
  let pos := certificateDenominator_pos
  (checkFace pos 100 1 1).physicalSideNormal pos i

def checkQ100FirstOffset (i : Fin 6) : CheckedReal certificateDenominator (q100FirstOffset i) :=
  let pos := certificateDenominator_pos
  (checkFace pos 100 1 1).derivativeNormalizedSideOffset pos 100 i

/-- Validate every pair's strict lens support on this supporting line. -/
def checkQ100FirstLenses (side : Fin 6) : Bool :=
  let normal := checkQ100FirstNormal side
  let offset := checkQ100FirstOffset side
  (List.finRange 48).all fun i => (List.finRange 48).all fun j =>
    if i < j then checkLensSupport certificateDenominator_pos checkQ100FirstCot
      (checkQ100FirstBody i) (checkQ100FirstBody j) normal offset else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
-- The finite proof scans all unordered pairs on the first supporting line.
theorem q100FirstLenses_side_zero : checkQ100FirstLenses 0 = true := by
  decide +kernel

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

/-- On the first supporting line and beyond, all distinct body pairs satisfy
the strict upper visual-angle bound. -/
theorem upperVisualAngle_q100_face_one_one_side_zero {p : Plane}
    (hp : q100FirstOffset 0 ≤ inner ℝ (q100FirstNormal 0) p) {i j : Fin 48} (different : i ≠ j) :
    angle (p - q100FirstBody i) (p - q100FirstBody j) < π - 81.841 * π / 180 := by
  wlog ordered : i < j generalizing i j
  · rw [angle_comm]
    exact this different.symm (lt_of_le_of_ne (le_of_not_gt ordered) different.symm)
  have h := q100FirstLenses_side_zero
  unfold checkQ100FirstLenses at h
  dsimp only at h
  have test := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i))
    j (List.mem_finRange j)
  rw [ite_eq_left ordered] at test
  have outside := visualLensValue_pos_of_check certificateDenominator_pos (by norm_num)
    (q100FirstBody_injective.ne different) checkQ100FirstCot (checkQ100FirstBody i)
    (checkQ100FirstBody j) (checkQ100FirstNormal 0) (checkQ100FirstOffset 0) hp test
  exact visualAngle_lt_supplement_of_outside_lens certificateOrientation
    (by positivity) (by linarith [pi_pos]) (by norm_num) q100FirstCot_lt outside

end Unfoldings.FewestNets
