module

public import Unfoldings.FewestNets.FiniteMeshCorner400Group01
public import Unfoldings.FewestNets.FiniteMeshCorner400Group02
public import Unfoldings.FewestNets.FiniteMeshCorner400Group03
public import Unfoldings.FewestNets.FiniteMeshCorner400Group04
public import Unfoldings.FewestNets.FiniteMeshCorner400Group05
public import Unfoldings.FewestNets.FiniteMeshCorner400Group06
public import Unfoldings.FewestNets.FiniteMeshCorner400Group07
public import Unfoldings.FewestNets.FiniteMeshCorner400Group08
public import Unfoldings.FewestNets.FiniteMeshCorner400Group09
public import Unfoldings.FewestNets.FiniteMeshCorner400Group10
public import Unfoldings.FewestNets.FiniteMeshCorner400Group11
public import Unfoldings.FewestNets.FiniteMeshCorner400Group12
public import Unfoldings.FewestNets.FiniteMeshCorner400Group13
public import Unfoldings.FewestNets.FiniteMeshCorner400Group14
public import Unfoldings.FewestNets.FiniteMeshCorner400Group15
public import Unfoldings.FewestNets.FiniteMeshCorner400Group16
public import Unfoldings.FewestNets.FiniteMeshCorner400Group17
public import Unfoldings.FewestNets.FiniteMeshCorner400Group18
public import Unfoldings.FewestNets.FiniteMeshCorner400Group19
public import Unfoldings.FewestNets.FiniteMeshCorner400Group20
public import Unfoldings.FewestNets.FiniteMeshCorner400Seam
public import Unfoldings.FewestNets.FiniteMeshCornerBlockCoverage

/-! Every frequency-400 canonical star passes the finite network corner checks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar Real

private theorem checkQ400FaceCornerBlock (i : Fin 278) :
    checkFaceCornerBlock 400 48 i 2200 108 = true := by
  let j : Fin 14 := ⟨i.val % 14, Nat.mod_lt _ (by decide)⟩
  have label : i.val = j.val + 14 * (i.val / 14) := by dsimp only [j]; omega
  have group : i.val / 14 ≤ 19 := by have := i.isLt; omega
  interval_cases (i.val / 14) <;> rw [label] <;> norm_num only
  · exact checkQ400FaceCornerBlocks_0 j
  · exact checkQ400FaceCornerBlocks_1 j
  · exact checkQ400FaceCornerBlocks_2 j
  · exact checkQ400FaceCornerBlocks_3 j
  · exact checkQ400FaceCornerBlocks_4 j
  · exact checkQ400FaceCornerBlocks_5 j
  · exact checkQ400FaceCornerBlocks_6 j
  · exact checkQ400FaceCornerBlocks_7 j
  · exact checkQ400FaceCornerBlocks_8 j
  · exact checkQ400FaceCornerBlocks_9 j
  · exact checkQ400FaceCornerBlocks_10 j
  · exact checkQ400FaceCornerBlocks_11 j
  · exact checkQ400FaceCornerBlocks_12 j
  · exact checkQ400FaceCornerBlocks_13 j
  · exact checkQ400FaceCornerBlocks_14 j
  · exact checkQ400FaceCornerBlocks_15 j
  · exact checkQ400FaceCornerBlocks_16 j
  · exact checkQ400FaceCornerBlocks_17 j
  · exact checkQ400FaceCornerBlocks_18 j
  · have short : j.val < 12 := by have := i.isLt; omega
    exact checkQ400FaceCornerBlocks_19 ⟨j, short⟩

/-- The second endpoint mesh uses the certified radius and angle at every
interior orbit representative. -/
theorem q400_face_corner_bounds {i j : ℕ} (key : (i, j) ∈ faceMeshKeys 400) (k : Fin 6) :
    let M := face 400 i j
    0 < inner ℝ M.direction (M.dual k) ∧
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 2200)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (108 * π / 180) := by
  obtain ⟨block, mem⟩ := exists_mem_keyBlock (size := 48) (n := 278)
    (by rw [normalMeshKeys_q100_q400.2.2.1]; decide) key
  exact (checkFace certificateDenominator_pos 400 i j).checkAllCorners_sound
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 2200)
    (checkIncidentCosine certificateDenominator_pos 108)
    (List.all_eq_true.mp (checkQ400FaceCornerBlock block) (i, j) mem) k

/-- The same inequalities hold at every seam orbit representative. -/
theorem q400_seam_corner_bounds {i : ℕ} (key : i ∈ seamMeshKeys 400) (k : Fin 6) :
    let M := seam 400 i
    0 < inner ℝ M.direction (M.dual k) ∧
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 2200)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (108 * π / 180) := by
  obtain ⟨block, mem⟩ := exists_mem_keyBlock (size := 48) (n := 5)
    (by rw [normalMeshKeys_q100_q400.2.2.2]; decide) key
  exact (checkSeam certificateDenominator_pos 400 i).checkAllCorners_sound
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 2200)
    (checkIncidentCosine certificateDenominator_pos 108)
    (List.all_eq_true.mp (checkQ400SeamCornerBlocks block) i mem) k

/-- The five corners of the original-vertex representative pass both checks. -/
theorem q400_pentagon_corner_bounds (k : Fin 5) :
    let M := pentagon 400
    0 < inner ℝ M.direction (M.dual k) ∧
    tan ((101 / 100 : ℝ) * (icosahedronEdge / 2200)) <
      meshCornerAltitude (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) ∧
    meshCornerCosine (M.cornerRay k (k - 1)) (M.cornerRay k (k + 1)) < cos (108 * π / 180) :=
  (checkPentagon certificateDenominator_pos 400).checkAllCorners_sound
    certificateDenominator_pos (checkGuardTangent certificateDenominator_pos 2200)
    (checkIncidentCosine certificateDenominator_pos 108) checkQ400PentagonCorners k

end Unfoldings.FewestNets
