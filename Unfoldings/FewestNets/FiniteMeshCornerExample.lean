module

public import Unfoldings.FewestNets.CheckedMeshCorner
public import Unfoldings.FewestNets.FiniteMeshExample

/-! Check the network corner inequalities on a canonical frequency-100 star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open Real CheckedReal

def checkIcosahedronEdge {D : ℕ} (hD : 0 < D) : CheckedReal D icosahedronEdge :=
  let sq5 := (rat D 5).sqrt hD
  let denominator := ((rat D 10).add ((rat D 2).mul hD sq5)).sqrt hD
  ((rat D 4).div hD denominator).convert (by simp [icosahedronEdge])

/-- Enclose the tangent of the guard radius for a separation of edge/denominator. -/
def checkGuardTangent {D : ℕ} (hD : 0 < D) (denominator : ℕ) :
    CheckedReal D (tan ((101 / 100 : ℝ) * (icosahedronEdge / denominator))) :=
  let r := ((rat D (101 / 100)).convert (by norm_num : ((101 / 100 : ℚ) : ℝ) =
    (101 / 100 : ℝ))).mul hD ((checkIcosahedronEdge hD).div hD (checkNat D denominator))
  ((r.checkSin hD 10).div hD (r.checkCos hD 10)).convert (by rw [tan_eq_sin_div_cos])

/-- Enclose the cosine of a whole number of degrees. -/
def checkIncidentCosine {D : ℕ} (hD : 0 < D) (degrees : ℕ) :
    CheckedReal D (cos ((degrees : ℝ) * π / 180)) :=
  let a := (((checkNat D degrees).mul hD (checkPi D)).div hD (checkNat D 180)).convert
    (by norm_num : (degrees : ℝ) * π / (180 : ℕ) = (degrees : ℝ) * π / 180)
  a.checkCos hD 20

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- All six corners of the example are computed in the kernel.
theorem checkCorners_q100_face_one_one (k : Fin 6) :
    (checkFace certificateDenominator_pos 100 1 1).checkCorner certificateDenominator_pos
      (checkGuardTangent certificateDenominator_pos 700)
      (checkIncidentCosine certificateDenominator_pos 107) k = true := by
  fin_cases k <;> decide +kernel

theorem corner_bounds_q100_face_one_one (k : Fin 6) :
    let M := face 100 1 1
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 700)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (107 * π / 180) := by
  exact (checkFace certificateDenominator_pos 100 1 1).corner_bounds_of_check
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 700)
    (checkIncidentCosine certificateDenominator_pos 107) k (checkCorners_q100_face_one_one k)

end Unfoldings.FewestNets.MeshStar
