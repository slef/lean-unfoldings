module

public import Unfoldings.FewestNets.MeshArcLength
public import Unfoldings.FewestNets.MeshBisectors

/-! Kernel-checked side bounds for a canonical frequency-100 site star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.MeshStar

open InnerProductGeometry

/-- The checker uses the same fixed-point denominator as the paper's replay. -/
def certificateDenominator : ℕ := 2 ^ 80

theorem certificateDenominator_pos : 0 < certificateDenominator := by
  unfold certificateDenominator
  positivity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The kernel reduces all six fixed-point side checks.
/-- The six bisector vertices at the canonical face key (1, 1) are outward
and their six candidate side lengths pass the algebraic bound. -/
theorem checkStar_q100_face_one_one :
    (checkFace certificateDenominator_pos 100 1 1).checkStar certificateDenominator_pos 100 =
      true := by
  decide +kernel

/-- The verified frequency-100 star has outward dual normals and short minor arcs. -/
theorem dualAngle_q100_face_one_one (i : Fin 6) :
    let M := face 100 1 1
    0 < inner ℝ M.direction (M.dual i) ∧
      angle (M.dualDirection i) (M.dualDirection (i + 1)) < 2 * (icosahedronEdge / 100) := by
  let M := face 100 1 1
  have checks (j : Fin 6) :=
    (checkFace certificateDenominator_pos 100 1 1).allDualSides_of_check
      certificateDenominator_pos checkStar_q100_face_one_one j
  exact ⟨(checks i).1, (dualAngle_le_dualArcUpper (star := M) i (fun j => (checks j).1)).trans_lt
    (checks i).2⟩

end Unfoldings.FewestNets.MeshStar
