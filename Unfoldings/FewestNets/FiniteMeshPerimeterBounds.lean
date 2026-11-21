module

public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks1
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks2
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks3
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks4
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks5
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks6
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks7
public import Unfoldings.FewestNets.FiniteMeshPerimeterBlocks8
public import Batteries.Data.List.Lemmas

/-! Assemble kernel-checked block enclosures for the canonical star perimeter. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

private theorem checkQ100FacePerimeterBlock_eq (i : Fin 70) :
    checkQ100FacePerimeterBlock i = true := by
  let j : Fin 10 := ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩
  have h : i.val = j.val + 10 * (i.val / 10) := by
    dsimp only [j]
    omega
  have group : i.val / 10 ≤ 6 := by have := i.isLt; omega
  interval_cases (i.val / 10) <;> rw [h] <;> norm_num only
  · exact checkQ100FacePerimeterBlocks_zero j
  · exact checkQ100FacePerimeterBlocks_1 j
  · exact checkQ100FacePerimeterBlocks_2 j
  · exact checkQ100FacePerimeterBlocks_3 j
  · exact checkQ100FacePerimeterBlocks_4 j
  · exact checkQ100FacePerimeterBlocks_5 j
  · exact checkQ100FacePerimeterBlocks_6 j

set_option maxRecDepth 8192 in
-- These blocks partition the key list in its original order.
private theorem q100FaceBlockCoverage :
    (List.ofFn (fun i : Fin 70 => faceMeshKeyBlock 100 12 i)).flatten = faceMeshKeys 100 := by
  decide +kernel

private theorem q100SeamBlockCoverage :
    (List.ofFn (fun i : Fin 5 => seamMeshKeyBlock 100 12 i)).flatten = seamMeshKeys 100 := by
  decide +kernel

private theorem sum_map_eq_sum_blocks {ι : Type*} {n : ℕ} {keys : List ι}
    {block : Fin n → List ι} (coverage : (List.ofFn block).flatten = keys) (f : ι → ℝ) :
    (keys.map f).sum = ∑ i, ((block i).map f).sum := by
  rw [← coverage, List.map_flatten, List.sum_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]

private theorem q100_face_perimeter_bound :
    ((faceMeshKeys 100).map (faceWeightedPerimeter 100)).sum ≤ (202682288 : ℝ) / 1000000 := by
  rw [sum_map_eq_sum_blocks q100FaceBlockCoverage]
  apply le_trans (Finset.sum_le_sum (fun i _ => (CheckedReal.lt_of_isLT
    certificateDenominator_pos _ _ (checkQ100FacePerimeterBlock_eq i)).le))
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast (show (∑ i : Fin 70, (q100FacePerimeterBounds[i.val]?).getD 0) ≤ 202682288 by
    decide +kernel)

private theorem q100_seam_perimeter_bound :
    ((seamMeshKeys 100).map (seamWeightedPerimeter 100)).sum ≤ (3796077 : ℝ) / 1000000 := by
  rw [sum_map_eq_sum_blocks q100SeamBlockCoverage]
  apply le_trans (Finset.sum_le_sum (fun i _ => (CheckedReal.lt_of_isLT
    certificateDenominator_pos _ _ (checkQ100SeamPerimeterBlocks i)).le))
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast (show (∑ i : Fin 5, (q100SeamPerimeterBounds[i.val]?).getD 0) ≤ 3796077 by
    decide +kernel)

/-- Kernel-certified upper bound on the frequency-100 weighted model-star perimeter. -/
theorem weightedArcUpperTotal_q100 : weightedArcUpperTotal 100 < 2084 := by
  have pent : (pentagon 100).arcUpperPerimeter < (32673 : ℝ) / 1000000 :=
    CheckedReal.lt_of_isLT certificateDenominator_pos _ _ checkQ100PentagonPerimeter_eq
  unfold weightedArcUpperTotal
  linarith only [q100_face_perimeter_bound, q100_seam_perimeter_bound, pent]

end Unfoldings.FewestNets
