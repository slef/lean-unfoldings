module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys00
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys01
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys02
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys03
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys04
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys05
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys06
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys07
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys08
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys09
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys10
public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Keys11

/-! Comprehensive coverage and soundness of the frequency-400 scalar table. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

def checkQ400DevelopmentScalarRow (row : KeyedDevelopmentScalar) : Bool :=
  row.2.check MeshStar.certificateDenominator_pos (832067 / 10000) &&
    checkDevelopmentCellTilt 400 row.1 row.2.tilt

structure Q400DevelopmentScalarBatch where
  offset : ℕ
  blocks : List (List KeyedDevelopmentScalar)
  keys : blocks.flatten.map Prod.fst = ((meshRecordKeys 400).drop offset).take 144
  checked : ∀ j : Fin blocks.length, (blocks.get j).all checkQ400DevelopmentScalarRow = true

/-- Use the checked slice for a given block of 144 canonical keys. -/
def q400DevelopmentScalarBatch : Fin 94 → Q400DevelopmentScalarBatch :=
  ![
    ⟨0, q400DevelopmentScalarGroup00, q400DevelopmentScalarGroup00_keys,
      fun j => q400DevelopmentScalarGroup00_checked ⟨j.val, j.isLt⟩⟩,
    ⟨144, q400DevelopmentScalarGroup01, q400DevelopmentScalarGroup01_keys,
      fun j => q400DevelopmentScalarGroup01_checked ⟨j.val, j.isLt⟩⟩,
    ⟨288, q400DevelopmentScalarGroup02, q400DevelopmentScalarGroup02_keys,
      fun j => q400DevelopmentScalarGroup02_checked ⟨j.val, j.isLt⟩⟩,
    ⟨432, q400DevelopmentScalarGroup03, q400DevelopmentScalarGroup03_keys,
      fun j => q400DevelopmentScalarGroup03_checked ⟨j.val, j.isLt⟩⟩,
    ⟨576, q400DevelopmentScalarGroup04, q400DevelopmentScalarGroup04_keys,
      fun j => q400DevelopmentScalarGroup04_checked ⟨j.val, j.isLt⟩⟩,
    ⟨720, q400DevelopmentScalarGroup05, q400DevelopmentScalarGroup05_keys,
      fun j => q400DevelopmentScalarGroup05_checked ⟨j.val, j.isLt⟩⟩,
    ⟨864, q400DevelopmentScalarGroup06, q400DevelopmentScalarGroup06_keys,
      fun j => q400DevelopmentScalarGroup06_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1008, q400DevelopmentScalarGroup07, q400DevelopmentScalarGroup07_keys,
      fun j => q400DevelopmentScalarGroup07_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1152, q400DevelopmentScalarGroup08, q400DevelopmentScalarGroup08_keys,
      fun j => q400DevelopmentScalarGroup08_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1296, q400DevelopmentScalarGroup09, q400DevelopmentScalarGroup09_keys,
      fun j => q400DevelopmentScalarGroup09_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1440, q400DevelopmentScalarGroup10, q400DevelopmentScalarGroup10_keys,
      fun j => q400DevelopmentScalarGroup10_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1584, q400DevelopmentScalarGroup11, q400DevelopmentScalarGroup11_keys,
      fun j => q400DevelopmentScalarGroup11_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1728, q400DevelopmentScalarGroup12, q400DevelopmentScalarGroup12_keys,
      fun j => q400DevelopmentScalarGroup12_checked ⟨j.val, j.isLt⟩⟩,
    ⟨1872, q400DevelopmentScalarGroup13, q400DevelopmentScalarGroup13_keys,
      fun j => q400DevelopmentScalarGroup13_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2016, q400DevelopmentScalarGroup14, q400DevelopmentScalarGroup14_keys,
      fun j => q400DevelopmentScalarGroup14_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2160, q400DevelopmentScalarGroup15, q400DevelopmentScalarGroup15_keys,
      fun j => q400DevelopmentScalarGroup15_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2304, q400DevelopmentScalarGroup16, q400DevelopmentScalarGroup16_keys,
      fun j => q400DevelopmentScalarGroup16_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2448, q400DevelopmentScalarGroup17, q400DevelopmentScalarGroup17_keys,
      fun j => q400DevelopmentScalarGroup17_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2592, q400DevelopmentScalarGroup18, q400DevelopmentScalarGroup18_keys,
      fun j => q400DevelopmentScalarGroup18_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2736, q400DevelopmentScalarGroup19, q400DevelopmentScalarGroup19_keys,
      fun j => q400DevelopmentScalarGroup19_checked ⟨j.val, j.isLt⟩⟩,
    ⟨2880, q400DevelopmentScalarGroup20, q400DevelopmentScalarGroup20_keys,
      fun j => q400DevelopmentScalarGroup20_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3024, q400DevelopmentScalarGroup21, q400DevelopmentScalarGroup21_keys,
      fun j => q400DevelopmentScalarGroup21_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3168, q400DevelopmentScalarGroup22, q400DevelopmentScalarGroup22_keys,
      fun j => q400DevelopmentScalarGroup22_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3312, q400DevelopmentScalarGroup23, q400DevelopmentScalarGroup23_keys,
      fun j => q400DevelopmentScalarGroup23_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3456, q400DevelopmentScalarGroup24, q400DevelopmentScalarGroup24_keys,
      fun j => q400DevelopmentScalarGroup24_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3600, q400DevelopmentScalarGroup25, q400DevelopmentScalarGroup25_keys,
      fun j => q400DevelopmentScalarGroup25_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3744, q400DevelopmentScalarGroup26, q400DevelopmentScalarGroup26_keys,
      fun j => q400DevelopmentScalarGroup26_checked ⟨j.val, j.isLt⟩⟩,
    ⟨3888, q400DevelopmentScalarGroup27, q400DevelopmentScalarGroup27_keys,
      fun j => q400DevelopmentScalarGroup27_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4032, q400DevelopmentScalarGroup28, q400DevelopmentScalarGroup28_keys,
      fun j => q400DevelopmentScalarGroup28_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4176, q400DevelopmentScalarGroup29, q400DevelopmentScalarGroup29_keys,
      fun j => q400DevelopmentScalarGroup29_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4320, q400DevelopmentScalarGroup30, q400DevelopmentScalarGroup30_keys,
      fun j => q400DevelopmentScalarGroup30_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4464, q400DevelopmentScalarGroup31, q400DevelopmentScalarGroup31_keys,
      fun j => q400DevelopmentScalarGroup31_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4608, q400DevelopmentScalarGroup32, q400DevelopmentScalarGroup32_keys,
      fun j => q400DevelopmentScalarGroup32_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4752, q400DevelopmentScalarGroup33, q400DevelopmentScalarGroup33_keys,
      fun j => q400DevelopmentScalarGroup33_checked ⟨j.val, j.isLt⟩⟩,
    ⟨4896, q400DevelopmentScalarGroup34, q400DevelopmentScalarGroup34_keys,
      fun j => q400DevelopmentScalarGroup34_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5040, q400DevelopmentScalarGroup35, q400DevelopmentScalarGroup35_keys,
      fun j => q400DevelopmentScalarGroup35_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5184, q400DevelopmentScalarGroup36, q400DevelopmentScalarGroup36_keys,
      fun j => q400DevelopmentScalarGroup36_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5328, q400DevelopmentScalarGroup37, q400DevelopmentScalarGroup37_keys,
      fun j => q400DevelopmentScalarGroup37_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5472, q400DevelopmentScalarGroup38, q400DevelopmentScalarGroup38_keys,
      fun j => q400DevelopmentScalarGroup38_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5616, q400DevelopmentScalarGroup39, q400DevelopmentScalarGroup39_keys,
      fun j => q400DevelopmentScalarGroup39_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5760, q400DevelopmentScalarGroup40, q400DevelopmentScalarGroup40_keys,
      fun j => q400DevelopmentScalarGroup40_checked ⟨j.val, j.isLt⟩⟩,
    ⟨5904, q400DevelopmentScalarGroup41, q400DevelopmentScalarGroup41_keys,
      fun j => q400DevelopmentScalarGroup41_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6048, q400DevelopmentScalarGroup42, q400DevelopmentScalarGroup42_keys,
      fun j => q400DevelopmentScalarGroup42_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6192, q400DevelopmentScalarGroup43, q400DevelopmentScalarGroup43_keys,
      fun j => q400DevelopmentScalarGroup43_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6336, q400DevelopmentScalarGroup44, q400DevelopmentScalarGroup44_keys,
      fun j => q400DevelopmentScalarGroup44_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6480, q400DevelopmentScalarGroup45, q400DevelopmentScalarGroup45_keys,
      fun j => q400DevelopmentScalarGroup45_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6624, q400DevelopmentScalarGroup46, q400DevelopmentScalarGroup46_keys,
      fun j => q400DevelopmentScalarGroup46_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6768, q400DevelopmentScalarGroup47, q400DevelopmentScalarGroup47_keys,
      fun j => q400DevelopmentScalarGroup47_checked ⟨j.val, j.isLt⟩⟩,
    ⟨6912, q400DevelopmentScalarGroup48, q400DevelopmentScalarGroup48_keys,
      fun j => q400DevelopmentScalarGroup48_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7056, q400DevelopmentScalarGroup49, q400DevelopmentScalarGroup49_keys,
      fun j => q400DevelopmentScalarGroup49_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7200, q400DevelopmentScalarGroup50, q400DevelopmentScalarGroup50_keys,
      fun j => q400DevelopmentScalarGroup50_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7344, q400DevelopmentScalarGroup51, q400DevelopmentScalarGroup51_keys,
      fun j => q400DevelopmentScalarGroup51_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7488, q400DevelopmentScalarGroup52, q400DevelopmentScalarGroup52_keys,
      fun j => q400DevelopmentScalarGroup52_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7632, q400DevelopmentScalarGroup53, q400DevelopmentScalarGroup53_keys,
      fun j => q400DevelopmentScalarGroup53_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7776, q400DevelopmentScalarGroup54, q400DevelopmentScalarGroup54_keys,
      fun j => q400DevelopmentScalarGroup54_checked ⟨j.val, j.isLt⟩⟩,
    ⟨7920, q400DevelopmentScalarGroup55, q400DevelopmentScalarGroup55_keys,
      fun j => q400DevelopmentScalarGroup55_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8064, q400DevelopmentScalarGroup56, q400DevelopmentScalarGroup56_keys,
      fun j => q400DevelopmentScalarGroup56_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8208, q400DevelopmentScalarGroup57, q400DevelopmentScalarGroup57_keys,
      fun j => q400DevelopmentScalarGroup57_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8352, q400DevelopmentScalarGroup58, q400DevelopmentScalarGroup58_keys,
      fun j => q400DevelopmentScalarGroup58_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8496, q400DevelopmentScalarGroup59, q400DevelopmentScalarGroup59_keys,
      fun j => q400DevelopmentScalarGroup59_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8640, q400DevelopmentScalarGroup60, q400DevelopmentScalarGroup60_keys,
      fun j => q400DevelopmentScalarGroup60_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8784, q400DevelopmentScalarGroup61, q400DevelopmentScalarGroup61_keys,
      fun j => q400DevelopmentScalarGroup61_checked ⟨j.val, j.isLt⟩⟩,
    ⟨8928, q400DevelopmentScalarGroup62, q400DevelopmentScalarGroup62_keys,
      fun j => q400DevelopmentScalarGroup62_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9072, q400DevelopmentScalarGroup63, q400DevelopmentScalarGroup63_keys,
      fun j => q400DevelopmentScalarGroup63_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9216, q400DevelopmentScalarGroup64, q400DevelopmentScalarGroup64_keys,
      fun j => q400DevelopmentScalarGroup64_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9360, q400DevelopmentScalarGroup65, q400DevelopmentScalarGroup65_keys,
      fun j => q400DevelopmentScalarGroup65_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9504, q400DevelopmentScalarGroup66, q400DevelopmentScalarGroup66_keys,
      fun j => q400DevelopmentScalarGroup66_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9648, q400DevelopmentScalarGroup67, q400DevelopmentScalarGroup67_keys,
      fun j => q400DevelopmentScalarGroup67_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9792, q400DevelopmentScalarGroup68, q400DevelopmentScalarGroup68_keys,
      fun j => q400DevelopmentScalarGroup68_checked ⟨j.val, j.isLt⟩⟩,
    ⟨9936, q400DevelopmentScalarGroup69, q400DevelopmentScalarGroup69_keys,
      fun j => q400DevelopmentScalarGroup69_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10080, q400DevelopmentScalarGroup70, q400DevelopmentScalarGroup70_keys,
      fun j => q400DevelopmentScalarGroup70_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10224, q400DevelopmentScalarGroup71, q400DevelopmentScalarGroup71_keys,
      fun j => q400DevelopmentScalarGroup71_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10368, q400DevelopmentScalarGroup72, q400DevelopmentScalarGroup72_keys,
      fun j => q400DevelopmentScalarGroup72_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10512, q400DevelopmentScalarGroup73, q400DevelopmentScalarGroup73_keys,
      fun j => q400DevelopmentScalarGroup73_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10656, q400DevelopmentScalarGroup74, q400DevelopmentScalarGroup74_keys,
      fun j => q400DevelopmentScalarGroup74_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10800, q400DevelopmentScalarGroup75, q400DevelopmentScalarGroup75_keys,
      fun j => q400DevelopmentScalarGroup75_checked ⟨j.val, j.isLt⟩⟩,
    ⟨10944, q400DevelopmentScalarGroup76, q400DevelopmentScalarGroup76_keys,
      fun j => q400DevelopmentScalarGroup76_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11088, q400DevelopmentScalarGroup77, q400DevelopmentScalarGroup77_keys,
      fun j => q400DevelopmentScalarGroup77_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11232, q400DevelopmentScalarGroup78, q400DevelopmentScalarGroup78_keys,
      fun j => q400DevelopmentScalarGroup78_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11376, q400DevelopmentScalarGroup79, q400DevelopmentScalarGroup79_keys,
      fun j => q400DevelopmentScalarGroup79_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11520, q400DevelopmentScalarGroup80, q400DevelopmentScalarGroup80_keys,
      fun j => q400DevelopmentScalarGroup80_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11664, q400DevelopmentScalarGroup81, q400DevelopmentScalarGroup81_keys,
      fun j => q400DevelopmentScalarGroup81_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11808, q400DevelopmentScalarGroup82, q400DevelopmentScalarGroup82_keys,
      fun j => q400DevelopmentScalarGroup82_checked ⟨j.val, j.isLt⟩⟩,
    ⟨11952, q400DevelopmentScalarGroup83, q400DevelopmentScalarGroup83_keys,
      fun j => q400DevelopmentScalarGroup83_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12096, q400DevelopmentScalarGroup84, q400DevelopmentScalarGroup84_keys,
      fun j => q400DevelopmentScalarGroup84_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12240, q400DevelopmentScalarGroup85, q400DevelopmentScalarGroup85_keys,
      fun j => q400DevelopmentScalarGroup85_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12384, q400DevelopmentScalarGroup86, q400DevelopmentScalarGroup86_keys,
      fun j => q400DevelopmentScalarGroup86_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12528, q400DevelopmentScalarGroup87, q400DevelopmentScalarGroup87_keys,
      fun j => q400DevelopmentScalarGroup87_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12672, q400DevelopmentScalarGroup88, q400DevelopmentScalarGroup88_keys,
      fun j => q400DevelopmentScalarGroup88_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12816, q400DevelopmentScalarGroup89, q400DevelopmentScalarGroup89_keys,
      fun j => q400DevelopmentScalarGroup89_checked ⟨j.val, j.isLt⟩⟩,
    ⟨12960, q400DevelopmentScalarGroup90, q400DevelopmentScalarGroup90_keys,
      fun j => q400DevelopmentScalarGroup90_checked ⟨j.val, j.isLt⟩⟩,
    ⟨13104, q400DevelopmentScalarGroup91, q400DevelopmentScalarGroup91_keys,
      fun j => q400DevelopmentScalarGroup91_checked ⟨j.val, j.isLt⟩⟩,
    ⟨13248, q400DevelopmentScalarGroup92, q400DevelopmentScalarGroup92_keys,
      fun j => q400DevelopmentScalarGroup92_checked ⟨j.val, j.isLt⟩⟩,
    ⟨13392, q400DevelopmentScalarGroup93, q400DevelopmentScalarGroup93_keys,
      fun j => q400DevelopmentScalarGroup93_checked ⟨j.val, j.isLt⟩⟩
  ]

private theorem q400DevelopmentScalarBatch_offset (i : Fin 94) :
    (q400DevelopmentScalarBatch i).offset = 144 * i.val := by
  fin_cases i <;> rfl

private theorem meshRecordKeys_length_q400 : (meshRecordKeys 400).length = 13534 := by
  simp only [meshRecordKeys, List.length_append, List.length_map, List.length_singleton,
    normalMeshKeys_q100_q400.2.2.1, normalMeshKeys_q100_q400.2.2.2]

/-- Every canonical key has a record with the checked analytic gaps and a valid tilt test. -/
theorem exists_q400DevelopmentScalarRecord_checked {key : MeshRecordKey}
    (mem : key ∈ meshRecordKeys 400) :
    ∃ (i : Fin 94) (record : DevelopmentScalarRecord),
      (key, record) ∈ (q400DevelopmentScalarBatch i).blocks.flatten ∧
      record.check MeshStar.certificateDenominator_pos (832067 / 10000) = true ∧
      checkDevelopmentCellTilt 400 key record.tilt = true := by
  obtain ⟨j, at_key⟩ := List.mem_iff_get.mp mem
  have bound : j.val < 13534 := by rw [← meshRecordKeys_length_q400]; exact j.isLt
  let i : Fin 94 := ⟨j.val / 144, by omega⟩
  let t := j.val % 144
  let batch := q400DevelopmentScalarBatch i
  have fits : t < (((meshRecordKeys 400).drop (144 * i.val)).take 144).length := by
    rw [List.length_take, List.length_drop, meshRecordKeys_length_q400]
    dsimp only [i, t]
    omega
  have same : (((meshRecordKeys 400).drop (144 * i.val)).take 144)[t]'fits = key := by
    rw [List.getElem_take, List.getElem_drop]
    have idx : 144 * i.val + t = j.val := by dsimp only [i, t]; omega
    simpa only [idx, List.get_eq_getElem] using at_key
  have in_slice : key ∈ batch.blocks.flatten.map Prod.fst := by
    rw [batch.keys, q400DevelopmentScalarBatch_offset, ← same]
    exact List.getElem_mem fits
  obtain ⟨⟨entry, record⟩, present, hk⟩ := List.mem_map.mp in_slice
  change entry = key at hk
  subst entry
  obtain ⟨block, has_block, in_block⟩ := List.mem_flatten.mp present
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp has_block
  have good := List.all_eq_true.mp (batch.checked k) (key, record) in_block
  simp only [checkQ400DevelopmentScalarRow, Bool.and_eq_true] at good
  exact ⟨i, record, present, good⟩

end Unfoldings.FewestNets
