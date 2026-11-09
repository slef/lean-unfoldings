module

public import Unfoldings.Complex.Regular

/-! Regular intrinsic edge points viewed from either side of a retained seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem isRegularPoint_seamSide (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face) (side : Bool)
    (x : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge)
    (regular : ¬ (C.triangle (C.seamSide s side).face).IsVertex x) :
    C.IsRegularPoint retain
      (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.seamSide s side) x)) := by
  cases side
  · exact C.isRegularPoint_hinge retain s kept different x regular
  · change (C.triangle (C.right s).face).Edge (C.right s).edge at x
    change ¬ (C.triangle (C.right s).face).IsVertex x at regular
    change C.IsRegularPoint retain
      (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.right s) x))
    let y := (C.identify s).symm x
    have left_regular : ¬ (C.triangle (C.left s).face).IsVertex y := fun vertex => regular
      (((C.triangle (C.right s).face).edge_isometry_isVertex_iff
        (C.triangle (C.left s).face) _ _ (C.identify s).symm x).mp vertex)
    have equal : MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) y) =
        MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.right s) x) := by
      calc
        _ = MetricGluing.point C.Cell (C.glue retain)
            (C.edgePoint (C.right s) (C.identify s y)) :=
          MetricGluing.point_eq_of_glue C.Cell ⟨s, kept, y, rfl, rfl⟩
        _ = _ := congrArg (fun z => MetricGluing.point C.Cell (C.glue retain)
          (C.edgePoint (C.right s) z)) ((C.identify s).apply_symm_apply x)
    rw [← equal]
    exact C.isRegularPoint_hinge retain s kept different y left_regular

end Unfoldings.TriangleComplex
