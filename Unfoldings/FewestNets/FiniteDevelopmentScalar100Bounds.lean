module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group1
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group2
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group3
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group4
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group5
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group6
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group7
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group8
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group9
public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Group10

/-! The complete scalar checks of the published frequency-100 development records. -/

@[expose] public section

namespace Unfoldings.FewestNets

private theorem checkQ100DevelopmentScalarBlock_of_lt (j : ℕ) (within : j < 74) :
    checkQ100DevelopmentScalarBlock j = true := by
  by_cases h1 : j < 8
  · simpa only [zero_add] using checkQ100DevelopmentScalarBlock_group1 ⟨j, h1⟩
  by_cases h2 : j < 16
  · simpa only [Nat.add_sub_of_le (show 8 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group2 ⟨j - 8, by omega⟩
  by_cases h3 : j < 24
  · simpa only [Nat.add_sub_of_le (show 16 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group3 ⟨j - 16, by omega⟩
  by_cases h4 : j < 32
  · simpa only [Nat.add_sub_of_le (show 24 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group4 ⟨j - 24, by omega⟩
  by_cases h5 : j < 40
  · simpa only [Nat.add_sub_of_le (show 32 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group5 ⟨j - 32, by omega⟩
  by_cases h6 : j < 48
  · simpa only [Nat.add_sub_of_le (show 40 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group6 ⟨j - 40, by omega⟩
  by_cases h7 : j < 56
  · simpa only [Nat.add_sub_of_le (show 48 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group7 ⟨j - 48, by omega⟩
  by_cases h8 : j < 64
  · simpa only [Nat.add_sub_of_le (show 56 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group8 ⟨j - 56, by omega⟩
  by_cases h9 : j < 72
  · simpa only [Nat.add_sub_of_le (show 64 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group9 ⟨j - 64, by omega⟩
  simpa only [Nat.add_sub_of_le (show 72 ≤ j by omega)] using
      checkQ100DevelopmentScalarBlock_group10 ⟨j - 72, by omega⟩

theorem q100DevelopmentScalarRecord_checked {row : KeyedDevelopmentScalar}
    (mem : row ∈ q100DevelopmentScalarChunks.flatten) :
    row.2.check MeshStar.certificateDenominator_pos 81 = true := by
  obtain ⟨block, present, within⟩ := List.mem_flatten.mp mem
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp present
  have len : q100DevelopmentScalarChunks.length = 74 := by rfl
  have jlt : j.val < 74 := len ▸ j.isLt
  have h := checkQ100DevelopmentScalarBlock_of_lt j.val jlt
  unfold checkQ100DevelopmentScalarBlock at h
  rw [getElem?_pos q100DevelopmentScalarChunks j.val j.isLt] at h
  exact checkDevelopmentScalar_of_mem_block h within

theorem exists_q100DevelopmentScalarRecord_checked {key : MeshRecordKey}
    (mem : key ∈ meshRecordKeys 100) :
    ∃ record : DevelopmentScalarRecord, (key, record) ∈ q100DevelopmentScalarChunks.flatten ∧
      record.check MeshStar.certificateDenominator_pos 81 = true := by
  rw [← q100DevelopmentScalarRecords_keys] at mem
  obtain ⟨⟨k, record⟩, present, same⟩ := List.mem_map.mp mem
  change k = key at same
  subst k
  exact ⟨record, present, q100DevelopmentScalarRecord_checked present⟩

theorem q100DevelopmentScalarRecord_tilt {row : KeyedDevelopmentScalar}
    (mem : row ∈ q100DevelopmentScalarChunks.flatten) :
    row.2.tilt = 763933 / 100000000 := by
  have h : (q100DevelopmentScalarChunks.all fun block =>
      block.all fun r => decide (r.2.tilt = 763933 / 100000000)) = true := by decide +kernel
  obtain ⟨block, present, within⟩ := List.mem_flatten.mp mem
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h block present) row within)

end Unfoldings.FewestNets
