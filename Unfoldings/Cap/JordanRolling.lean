module

public import Unfoldings.Cap.JordanBankTurnBounds
public import Unfoldings.Complex.AffineProjectionBoundary
public import Unfoldings.Development.AffineProjection
public import Unfoldings.Development.BoundaryRolling

/-!
# Intrinsic and projected rolling of the actual Jordan bank

The projected complex is constructed from the same physical triangles and seam
names, with a genuine identity development. Its rolled real headings are thus
headings of the actual geometric bank. The intrinsic bank uses its original
edge lengths and fan turns instead.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

open Classical in
def jordanProjectedComplex (J : Set Plane) :
    TriangleComplex.{u, v} {f : Face // f ∈ K.jordanFaces J} :=
  (C.restrictFaces (K.jordanFaces J)).affineProjectionComplex
    (fun f => K.projectFaceEquiv f.val) (fun s x => K.projectedTriangle_joined s.val x)

open Classical in
/-- This identity placement uses the projected metric, with the actual planar bank positions. -/
def jordanProjectedDevelopment (J : Set Plane) :
    FacewiseDevelopment (K.jordanProjectedComplex J) Set.univ :=
  (C.restrictFaces (K.jordanFaces J)).affineProjectionDevelopment
    (fun f => K.projectFaceEquiv f.val) (fun s x => K.projectedTriangle_joined s.val x) (by
      intro f g different
      exact K.projectedTriangles_nonoverlapping (fun same => different (Subtype.ext same)))

variable {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- The projected bank visits the identical original edges and corner fans in the same order. -/
def jordanProjectedContour : (K.jordanProjectedComplex J).BoundaryContour Set.univ :=
  (C.restrictFaces (K.jordanFaces J)).affineProjectionContour
    (fun f => K.projectFaceEquiv f.val) (fun s x => K.projectedTriangle_joined s.val x) Set.univ
    (K.jordanContour jordan contains avoids)

open Classical in
/-- A projected vertex fan has its actual projected corner-angle sum. -/
theorem jordan_projected_fan_angle
    (w : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ) :
    (K.jordanProjectedComplex J).totalAngle Set.univ
      ((C.restrictFaces (K.jordanFaces J)).affineProjectionVertexEquiv
        (fun f => K.projectFaceEquiv f.val) (fun s x => K.projectedTriangle_joined s.val x)
        Set.univ w) =
      (C.restrictFaces (K.jordanFaces J)).regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w := by
  have angles := (C.restrictFaces (K.jordanFaces J)).affineProjection_totalAngle
    (fun f => K.projectFaceEquiv f.val) (fun s x => K.projectedTriangle_joined s.val x) Set.univ w
  have triangles (f : {f : Face // f ∈ K.jordanFaces J}) :
      (C.restrictFaces (K.jordanFaces J)).affineProjectedTriangle
        (fun f => K.projectFaceEquiv f.val) f = K.projectedTriangle f.val := rfl
  simp only [triangles] at angles
  simp only [jordanProjectedComplex, TriangleComplex.regionalCornerSum,
    Set.mem_univ, true_and]
  convert angles using 1
  rfl

open Classical in
/-- Real heading discrepancy of the actual intrinsically rolled and projected bank links. -/
def jordanRollHeadingError
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) : ℝ :=
  (C.restrictFaces (K.jordanFaces J)).boundaryRollHeading
    (K.jordanContour jordan contains avoids) i -
      (K.jordanProjectedComplex J).boundaryRollHeading
        (K.jordanProjectedContour jordan contains avoids) i

include jordan contains avoids in
open Classical in
/-- The real heading error is the cumulative actual one-sided fan-turn discrepancy. -/
theorem jordanRollHeadingError_eq_partialSum
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    K.jordanRollHeadingError jordan contains avoids i =
      Fin.partialSum (fun k => K.jordanContourTurnError jordan contains avoids k.succ) i := by
  classical
  let R := C.restrictFaces (K.jordanFaces J)
  let Q := K.jordanContour jordan contains avoids
  let P := K.jordanProjectedComplex J
  let fan (w : R.Vertex Set.univ) := P.totalAngle Set.univ
    (R.affineProjectionVertexEquiv (fun f => K.projectFaceEquiv f.val)
      (fun s x => K.projectedTriangle_joined s.val x) Set.univ w)
  change Fin.partialSum (fun k : Fin Q.length =>
    Real.pi - R.totalAngle Set.univ (R.boundaryEndVertex Set.univ (Q.cycle.point k.succ))) i -
      Fin.partialSum (fun k : Fin Q.length =>
        Real.pi - fan (R.boundaryEndVertex Set.univ (Q.cycle.point k.succ))) i = _
  refine Fin.induction ?_ (fun k previous => ?_) i
  · rw [Fin.partialSum_zero, Fin.partialSum_zero, Fin.partialSum_zero, sub_self]
  · rw [Fin.partialSum_succ, Fin.partialSum_succ, Fin.partialSum_succ]
    have angle := K.jordan_projected_fan_angle
      (R.boundaryEndVertex Set.univ (Q.cycle.point k.succ))
    change fan (R.boundaryEndVertex Set.univ (Q.cycle.point k.succ)) = _ at angle
    rw [angle]
    change _ = Fin.partialSum _ k.castSucc +
      ((Real.pi - R.totalAngle Set.univ (R.boundaryEndVertex Set.univ (Q.cycle.point k.succ))) -
        (Real.pi - R.regionalCornerSum Set.univ
          (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
          (R.boundaryEndVertex Set.univ (Q.cycle.point k.succ))))
    linarith

end Unfoldings.ConvexCap
