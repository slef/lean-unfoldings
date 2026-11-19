module

public import Unfoldings.Geometry.Barycentric

/-! Whole intrinsic half-plane balls in the original triangle edge coordinates. -/

@[expose] public section

namespace Unfoldings.Triangle

/-- The actual closed supporting half-plane on the triangle's occupied side of an edge. -/
def edgeHalfPlane (T : Triangle) (e : Fin 3) : Set Plane :=
  {p | 0 ≤ T.coord (next (next e)) p}

/-- An original edge point is on the boundary line of its supporting half-plane. -/
def edgeHalfPlanePoint (T : Triangle) (e : Fin 3) (x : T.Edge e) : T.edgeHalfPlane e :=
  ⟨x.val, by change 0 ≤ T.coord (next (next e)) x.val; rw [T.coord_edge_eq_zero e x]⟩

/-- The original edge half-ball is literally a whole ball of its occupied half-plane metric. -/
def edgeHalfPlaneBallIsometry (T : Triangle) (e : Fin 3) (x : T.Edge e) (r : ℝ) :
    T.edgeHalfBall e x r ≃ᵢ Metric.ball (T.edgeHalfPlanePoint e x) r where
  toFun p := ⟨⟨p.val, p.property.2⟩, p.property.1⟩
  invFun q := ⟨q.val.val, q.property, q.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun _ _ := rfl

end Unfoldings.Triangle
