module

public import Unfoldings.Geometry.RayAvoidance

/-! A genuine auxiliary triangle containing any prescribed nondegenerate segment as edge zero. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def thirdPoint (a b : Plane) (different : a ≠ b) : Plane :=
  (AffineArrangement.dense_nonzero (orientMap a b) (orientMap_ne_zero different)).nonempty.choose

theorem orient_thirdPoint_ne_zero (a b : Plane) (different : a ≠ b) :
    orient a b (thirdPoint a b different) ≠ 0 := by
  simpa only [thirdPoint, orientMap_apply, Set.mem_ofPred_eq] using
    (AffineArrangement.dense_nonzero (orientMap a b)
      (orientMap_ne_zero different)).nonempty.choose_spec

def triangleWithEdge (a b : Plane) (different : a ≠ b) : Triangle where
  vertex := ![a, b, thirdPoint a b different]
  nondegenerate := orient_thirdPoint_ne_zero a b different

theorem triangleWithEdge_edge_zero (a b : Plane) (different : a ≠ b) :
    (triangleWithEdge a b different).edge 0 = segment ℝ a b := rfl

end Unfoldings
