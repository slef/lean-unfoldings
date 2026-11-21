module

public import Unfoldings.FewestNets.FiniteDevelopmentScalar100Bounds
public import Unfoldings.FewestNets.IcosahedronLabeledStars
public import Unfoldings.FewestNets.IcosahedronMeshTilt
public import Unfoldings.FewestNets.VoronoiNetwork

/-! Each actual frequency-100 cell has the checked scalars of its canonical model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar InnerProductGeometry

/-- The record table forgets which actual macroface, edge, or vertex realizes the model. -/
def perimeterIndexRecordKey {q : ℕ} (label : PerimeterIndex q) : MeshRecordKey :=
  match label with
  | .inl p =>
    let key := (faceMeshKeys q).get p.2.1
    .face key.1 key.2
  | .inr (.inl p) => .seam ((seamMeshKeys q).get p.2.1)
  | .inr (.inr _) => .vertex

theorem perimeterIndexRecordKey_mem {q : ℕ} (label : PerimeterIndex q) :
    perimeterIndexRecordKey label ∈ meshRecordKeys q := by
  rcases label with p | (p | p)
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨(faceMeshKeys q).get p.2.1, List.get_mem _ _, rfl⟩))
  · exact List.mem_append_right _
      (List.mem_map.mpr ⟨(seamMeshKeys q).get p.2.1, List.get_mem _ _, rfl⟩)
  · exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self MeshRecordKey.vertex))

/-- The development constants for an actual cell satisfy all checked scalar
inequalities. The record tilt bounds all normals in that cell. -/
theorem exists_q100CellDevelopmentScalars (a : meshSites 100) :
    ∃ (label : PerimeterIndex 100) (record : DevelopmentScalarRecord),
      perimeterIndexRealizes a label ∧
      (perimeterIndexRecordKey label, record) ∈ q100DevelopmentScalarChunks.flatten ∧
      (∀ N ∈ sphericalVoronoiCell (fun b : meshSites 100 => (b : Space)) a,
        angle (a : Space) N ≤ record.tilt) ∧
      record.ValidFor 81 ∧
      (∀ i : Fin 3, 0 < developmentGaps record.tilt record.margin record.lengthConstant i) ∧
      0 < record.cotangentGap ∧ 0 < record.interiorMarginGap 81 := by
  have hq : (0 : ℕ) < 100 := by decide
  obtain ⟨label, _, realized⟩ := exists_perimeterIndex_realizing hq a
  obtain ⟨record, row, check⟩ :=
    exists_q100DevelopmentScalarRecord_checked (perimeterIndexRecordKey_mem label)
  refine ⟨label, record, realized, row, ?_, record.bounds_of_check certificateDenominator_pos 81
    check⟩
  intro N inside
  have unit : ‖N‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using inside.2
  rw [angle_comm]
  apply (angle_le_meshTilt_of_mem_normalCone hq unit a inside.1).trans
  have same : record.tilt = 763933 / 100000000 := q100DevelopmentScalarRecord_tilt row
  rw [same, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat]
  exact q100UniformTilt_le_recordTilt

end Unfoldings.FewestNets.Icosahedron
