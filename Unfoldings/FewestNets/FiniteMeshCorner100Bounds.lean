module

public import Unfoldings.FewestNets.FiniteMeshCorner100Group1
public import Unfoldings.FewestNets.FiniteMeshCorner100Group2
public import Unfoldings.FewestNets.FiniteMeshCorner100Group3
public import Unfoldings.FewestNets.FiniteMeshCorner100Group4
public import Unfoldings.FewestNets.FiniteMeshCorner100Group5
public import Unfoldings.FewestNets.FiniteMeshCorner100Group6
public import Unfoldings.FewestNets.FiniteMeshCorner100Group7
public import Unfoldings.FewestNets.FiniteMeshCorner100Seam
public import Unfoldings.FewestNets.FiniteMeshCornerBlockCoverage

/-! Every frequency-100 canonical star passes the finite network corner checks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar Real

private theorem checkQ100FaceCornerBlock (i : Fin 70) :
    checkFaceCornerBlock 100 12 i 700 107 = true := by
  let j : Fin 10 := ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩
  have label : i.val = j.val + 10 * (i.val / 10) := by dsimp only [j]; omega
  have group : i.val / 10 ≤ 6 := by have := i.isLt; omega
  interval_cases (i.val / 10) <;> rw [label] <;> norm_num only
  · exact checkQ100FaceCornerBlocks_0 j
  · exact checkQ100FaceCornerBlocks_1 j
  · exact checkQ100FaceCornerBlocks_2 j
  · exact checkQ100FaceCornerBlocks_3 j
  · exact checkQ100FaceCornerBlocks_4 j
  · exact checkQ100FaceCornerBlocks_5 j
  · exact checkQ100FaceCornerBlocks_6 j

/-- The first endpoint mesh uses the certified radius and angle at every
interior orbit representative. -/
theorem q100_face_corner_bounds {i j : ℕ} (key : (i, j) ∈ faceMeshKeys 100) (k : Fin 6) :
    let M := face 100 i j
    0 < inner ℝ M.direction (M.dual k) ∧
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 700)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (107 * π / 180) := by
  obtain ⟨block, mem⟩ := exists_mem_keyBlock (size := 12) (n := 70)
    (by rw [normalMeshKeys_q100_q400.1]; decide) key
  exact (checkFace certificateDenominator_pos 100 i j).checkAllCorners_sound
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 700)
    (checkIncidentCosine certificateDenominator_pos 107)
    (List.all_eq_true.mp (checkQ100FaceCornerBlock block) (i, j) mem) k

/-- The same inequalities hold at every seam orbit representative. -/
theorem q100_seam_corner_bounds {i : ℕ} (key : i ∈ seamMeshKeys 100) (k : Fin 6) :
    let M := seam 100 i
    0 < inner ℝ M.direction (M.dual k) ∧
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 700)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (107 * π / 180) := by
  obtain ⟨block, mem⟩ := exists_mem_keyBlock (size := 12) (n := 5)
    (by rw [normalMeshKeys_q100_q400.2.1]; decide) key
  exact (checkSeam certificateDenominator_pos 100 i).checkAllCorners_sound
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 700)
    (checkIncidentCosine certificateDenominator_pos 107)
    (List.all_eq_true.mp (checkQ100SeamCornerBlocks block) i mem) k

/-- The five corners of the original-vertex representative pass both checks. -/
theorem q100_pentagon_corner_bounds (k : Fin 5) :
    let M := pentagon 100
    0 < inner ℝ M.direction (M.dual k) ∧
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 700)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (107 * π / 180) :=
  (checkPentagon certificateDenominator_pos 100).checkAllCorners_sound
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 700)
    (checkIncidentCosine certificateDenominator_pos 107) checkQ100PentagonCorners k

end Unfoldings.FewestNets
