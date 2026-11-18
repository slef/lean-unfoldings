module

public import Unfoldings.Geometry.BankGapPlanarCells
public import Unfoldings.Metric.IsometricCells
public import Unfoldings.Metric.HalfOpenIntervalExtension

/-! Actual gap cells, closed bank edges and whole tails retain exact closed intrinsic embeddings. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ n} (M : BankGapModel first second)

/-- Original planar coordinates rule out all intrinsic shortcuts inside an actual gap cell. -/
theorem planarCell_intrinsic_isometry (i : M.Cell) :
    Isometry (fun p : M.planarCells i => M.planarCellIsometry
      (MetricGluing.of (fun i => M.planarCells i)
        (MetricGluing.distinctCoincident M.planarCells) i p)) := by
  apply M.planarCellIsometry.isometry.comp
  apply MetricGluing.of_isometry_of_compatible (fun i => M.planarCells i)
    (MetricGluing.distinctCoincident M.planarCells) (fun _ p => p.val)
  · intro _ _ _
    rfl
  · intro _ _ joined
    exact joined.2

/-- Every original gap-cell image is closed in the complete intrinsic gap. -/
theorem planarCell_intrinsic_isClosedEmbedding (i : M.Cell) :
    Topology.IsClosedEmbedding (fun p : M.planarCells i => M.planarCellIsometry
      (MetricGluing.of (fun i => M.planarCells i)
        (MetricGluing.distinctCoincident M.planarCells) i p)) := by
  let : CompleteSpace (M.planarCells i) := (M.planarCells_closed i).isComplete.completeSpace_coe
  exact (M.planarCell_intrinsic_isometry i).isClosedEmbedding

/-- A genuine actual closed bank edge is an intrinsic dilation at its original full speed. -/
def edgeDilation (side : Bool) (i : Fin n) (nonzero : (M.bank side).chain.edge i ≠ 0) :
    unitInterval →ᵈ PolygonalPoint M.region where
  toFun := M.edgePoint side i
  edist_eq' := ⟨‖(M.bank side).chain.edge i‖₊, nnnorm_ne_zero_iff.mpr nonzero,
    M.edist_edgePoint side i⟩

/-- A genuine actual infinite bank tail is an intrinsic dilation at its original full speed. -/
def tailDilation (side : Bool) (nonzero : (M.bank side).direction ≠ 0) :
    ℝ≥0 →ᵈ PolygonalPoint M.region where
  toFun := M.tailPoint side
  edist_eq' := ⟨‖(M.bank side).direction‖₊, nnnorm_ne_zero_iff.mpr nonzero,
    M.edist_tailPoint side⟩

theorem edgePoint_isClosedEmbedding (side : Bool) (i : Fin n)
    (nonzero : (M.bank side).chain.edge i ≠ 0) :
    Topology.IsClosedEmbedding (M.edgePoint side i) :=
  Dilation.isClosedEmbedding (M.edgeDilation side i nonzero)

theorem tailPoint_isClosedEmbedding (side : Bool) (nonzero : (M.bank side).direction ≠ 0) :
    Topology.IsClosedEmbedding (M.tailPoint side) :=
  Dilation.isClosedEmbedding (M.tailDilation side nonzero)

end Unfoldings.BankGapModel
