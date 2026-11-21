module

public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group01
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group02
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group03
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group04
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group05
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group06
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group07
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group08
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group09
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group10
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group11
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group12
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group13
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group14
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group15
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group16
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group17
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group18
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group19
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Group20
public import Unfoldings.FewestNets.FiniteMeshPerimeter400Seam
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlockSum

/-! Assemble the frequency-400 weighted perimeter from kernel-checked blocks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

private theorem checkQ400FacePerimeterBlock_eq (i : Fin 278) :
    checkQ400FacePerimeterBlock i = true := by
  let j : Fin 14 := ⟨i.val % 14, Nat.mod_lt _ (by decide)⟩
  have decompose : i.val = j.val + 14 * (i.val / 14) := by
    dsimp only [j]
    omega
  have group : i.val / 14 ≤ 19 := by have := i.isLt; omega
  interval_cases (i.val / 14) <;> rw [decompose] <;> norm_num only
  · exact checkQ400FacePerimeterBlocks_0 j
  · exact checkQ400FacePerimeterBlocks_1 j
  · exact checkQ400FacePerimeterBlocks_2 j
  · exact checkQ400FacePerimeterBlocks_3 j
  · exact checkQ400FacePerimeterBlocks_4 j
  · exact checkQ400FacePerimeterBlocks_5 j
  · exact checkQ400FacePerimeterBlocks_6 j
  · exact checkQ400FacePerimeterBlocks_7 j
  · exact checkQ400FacePerimeterBlocks_8 j
  · exact checkQ400FacePerimeterBlocks_9 j
  · exact checkQ400FacePerimeterBlocks_10 j
  · exact checkQ400FacePerimeterBlocks_11 j
  · exact checkQ400FacePerimeterBlocks_12 j
  · exact checkQ400FacePerimeterBlocks_13 j
  · exact checkQ400FacePerimeterBlocks_14 j
  · exact checkQ400FacePerimeterBlocks_15 j
  · exact checkQ400FacePerimeterBlocks_16 j
  · exact checkQ400FacePerimeterBlocks_17 j
  · exact checkQ400FacePerimeterBlocks_18 j
  · have short : j.val < 12 := by have := i.isLt; omega
    exact checkQ400FacePerimeterBlocks_19 ⟨j, short⟩

set_option maxRecDepth 8192 in
-- Sum the bounds only; the spatial interval arithmetic is already checked.
private theorem q400_face_perimeter_bound :
    ((faceMeshKeys 400).map (faceWeightedPerimeter 400)).sum ≤ (827849016 : ℝ) / 1000000 := by
  rw [sum_map_eq_sum_keyBlocks _ 48 278 (by rw [normalMeshKeys_q100_q400.2.2.1]; decide)]
  apply le_trans (Finset.sum_le_sum (fun i _ => (CheckedReal.lt_of_isLT
    certificateDenominator_pos _ _ (checkQ400FacePerimeterBlock_eq i)).le))
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast (show (∑ i : Fin 278, (q400FacePerimeterBounds[i.val]?).getD 0) ≤ 827849016 by
    decide +kernel)

private theorem q400_seam_perimeter_bound :
    ((seamMeshKeys 400).map (seamWeightedPerimeter 400)).sum ≤ (3813991 : ℝ) / 1000000 := by
  rw [sum_map_eq_sum_keyBlocks _ 48 5 (by rw [normalMeshKeys_q100_q400.2.2.2]; decide)]
  apply le_trans (Finset.sum_le_sum (fun i _ => (CheckedReal.lt_of_isLT
    certificateDenominator_pos _ _ (checkQ400SeamPerimeterBlocks i)).le))
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast (show (∑ i : Fin 5, (q400SeamPerimeterBounds[i.val]?).getD 0) ≤ 3813991 by
    decide +kernel)

/-- Kernel-certified upper bound on the frequency-400 weighted model-star perimeter. -/
theorem weightedArcUpperTotal_q400 : weightedArcUpperTotal 400 < 8336 := by
  have pent : (pentagon 400).arcUpperPerimeter < (8136 : ℝ) / 1000000 :=
    CheckedReal.lt_of_isLT certificateDenominator_pos _ _ checkQ400PentagonPerimeter_eq
  unfold weightedArcUpperTotal
  linarith only [q400_face_perimeter_bound, q400_seam_perimeter_bound, pent]

end Unfoldings.FewestNets
