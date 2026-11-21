module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar400Bounds
public import Unfoldings.FewestNets.IcosahedronFrequency400Tilt

/-! Each actual frequency-400 cell has the checked scalars and tilt of its own model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar InnerProductGeometry

/-- The canonical record applies to every actual site, including the tighter
local tilt bounds that some frequency-400 records require. -/
theorem exists_q400CellDevelopmentScalars (a : meshSites 400) :
    ∃ (label : PerimeterIndex 400) (i : Fin 94) (record : DevelopmentScalarRecord),
      perimeterIndexRealizes a label ∧
      (perimeterIndexRecordKey label, record) ∈ (q400DevelopmentScalarBatch i).blocks.flatten ∧
      (∀ N ∈ sphericalVoronoiCell (fun b : meshSites 400 => (b : Space)) a,
        angle (a : Space) N ≤ record.tilt) ∧
      record.ValidFor (832067 / 10000) ∧
      (∀ i : Fin 3, 0 < developmentGaps record.tilt record.margin record.lengthConstant i) ∧
      0 < record.cotangentGap ∧ 0 < record.interiorMarginGap (832067 / 10000) := by
  have hq : (0 : ℕ) < 400 := by decide
  obtain ⟨label, _, realized⟩ := exists_perimeterIndex_realizing hq a
  obtain ⟨batch, record, row, check, tilt⟩ :=
    exists_q400DevelopmentScalarRecord_checked (perimeterIndexRecordKey_mem label)
  have bounds := record.bounds_of_check certificateDenominator_pos (832067 / 10000) check
  refine ⟨label, batch, record, realized, row, ?_, bounds⟩
  intro N inside
  exact angle_le_of_q400_developmentCellTilt label realized bounds.1.1.le tilt inside

end Unfoldings.FewestNets.Icosahedron
