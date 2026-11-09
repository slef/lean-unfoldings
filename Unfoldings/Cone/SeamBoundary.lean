module

public import Unfoldings.Geometry.Corner
public import Unfoldings.Cone.Radial

/-!
# The actual radial banks at a retained seam

A bank is specified by the barycentric coordinate vanishing on its supporting
edge line. Both radial seam points lie on the banks determined by the actual
endpoint germs, including endpoint reversals.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- The coordinate vanishing on the incident bank selected by the link-germ Boolean. -/
def bankCoord (T : Triangle) (i : Fin 3) (side : Bool) (p : Plane) : ℝ :=
  if side then T.coord (next i) p else T.coord (next (next i)) p

theorem bankCoord_endpoint (T : Triangle) (e : Fin 3) (b : Bool) (p : Plane) :
    T.bankCoord (if b then next e else e) b p = T.coord (next (next e)) p := by
  cases b <;> rfl

theorem coord_radial_edge_zero (T : Triangle) (e : Fin 3) (b : Bool) (x : T.Edge e) (t : ℝ) :
    T.coord (next (next e)) (AffineMap.lineMap (T.endpoint e b).val x.val t) = 0 := by
  rw [(T.coord (next (next e))).apply_lineMap,
    T.coord_edge_eq_zero e (T.endpoint e b), T.coord_edge_eq_zero e x]
  simp

end Unfoldings.Triangle

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangentLeftPoint_bankCoord (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    (C.triangle (C.tangentLeft retain v s).val.1).bankCoord
      (C.tangentLeft retain v s).val.2 s.val.2.2
      (C.tangentLeftPoint retain v s x t nonnegative).val = 0 := by
  change (C.triangle (C.seamSide s.val.1 s.val.2.1).face).bankCoord
    (if s.val.2.2 then Triangle.next (C.seamSide s.val.1 s.val.2.1).edge
      else (C.seamSide s.val.1 s.val.2.1).edge) s.val.2.2
    (AffineMap.lineMap (C.tangentApex retain v (C.tangentLeft retain v s)).val x.val t) = 0
  rw [Triangle.bankCoord_endpoint, C.tangentLeft_apex_endpoint]
  exact Triangle.coord_radial_edge_zero _ _ _ x t

theorem tangentRightPoint_bankCoord (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) (t : ℝ) (nonnegative : 0 ≤ t) :
    (C.triangle (C.tangentRight retain v s).val.1).bankCoord
      (C.tangentRight retain v s).val.2 (C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)
      (C.tangentRightPoint retain v s x t nonnegative).val = 0 := by
  change (C.triangle (C.seamSide s.val.1 (!s.val.2.1)).face).bankCoord
    (if C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2 then
      Triangle.next (C.seamSide s.val.1 (!s.val.2.1)).edge
      else (C.seamSide s.val.1 (!s.val.2.1)).edge)
    (C.acrossEndpoint s.val.1 s.val.2.1 s.val.2.2)
    (AffineMap.lineMap (C.tangentApex retain v (C.tangentRight retain v s)).val
      (C.across s.val.1 s.val.2.1 x).val t) = 0
  rw [Triangle.bankCoord_endpoint, C.tangentRight_apex_endpoint]
  exact Triangle.coord_radial_edge_zero _ _ _ _ t

end Unfoldings.TriangleComplex
