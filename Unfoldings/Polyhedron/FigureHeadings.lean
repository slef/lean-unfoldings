module

public import Unfoldings.Polyhedron.FigureGlobalFrame
public import Unfoldings.Geometry.ComplexTurn

/-! Exact cumulative real headings of the actual figure polygon in one rigid frame. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

def figureDevelopFrame
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    Plane ≃ₗᵢ[ℝ] ℂ := (P.figureCentralFrame V c closes 0).place.linearIsometryEquiv

theorem figureDevelopFrame_agrees
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) (p : Plane) :
    P.figureDevelopFrame V c closes p = (P.figureCentralFrame V c closes 0).place p := by
  have decomposition := congrFun (P.figureCentralFrame V c closes 0).place.toAffineMap.decomp p
  change (P.figureCentralFrame V c closes 0).place p =
    P.figureDevelopFrame V c closes p + (P.figureCentralFrame V c closes 0).place 0 at decomposition
  rw [P.figureCentralFrame_zero, add_zero] at decomposition
  exact decomposition.symm

theorem figureDevelopFrame_angle
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    InnerProductGeometry.angle (P.figureDevelopFrame V c closes (V.linkPolygon c i))
      (P.figureDevelopFrame V c closes (V.linkPolygon c (finRotate (n + 1) i))) =
      (P.figureCentralFan V c closes).angle i := by
  change _ = InnerProductGeometry.angle (V.linkPolygon c i - 0)
    (V.linkPolygon c (finRotate (n + 1) i) - 0)
  simp only [sub_zero]
  exact (P.figureDevelopFrame V c closes).toLinearIsometry.angle_map _ _

theorem figureDevelopFrame_polar_successor
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) (θ : ℝ)
    (first : P.figureDevelopFrame V c closes (V.linkPolygon c i) =
      (‖V.linkPolygon c i‖ : ℂ) * polarRay θ) :
    P.figureDevelopFrame V c closes (V.linkPolygon c (finRotate (n + 1) i)) =
      (‖V.linkPolygon c (finRotate (n + 1) i)‖ : ℂ) *
        polarRay (θ + (P.figureCentralFan V c closes).angle i) := by
  have positive := P.figureCentralFrame_cross_positive V c closes i
  rw [← P.figureDevelopFrame_agrees, ← P.figureDevelopFrame_agrees] at positive
  have initial : P.figureDevelopFrame V c closes (V.linkPolygon c i) =
      (‖P.figureDevelopFrame V c closes (V.linkPolygon c i)‖ : ℂ) * polarRay θ := by
    simpa only [(P.figureDevelopFrame V c closes).norm_map] using first
  have successor := polar_successor_of_positive_cross θ initial positive
  simpa only [(P.figureDevelopFrame V c closes).norm_map,
    P.figureDevelopFrame_angle] using successor

theorem figureDevelopFrame_heading
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    P.figureDevelopFrame V c closes (V.linkPolygon c i) =
      (‖V.linkPolygon c i‖ : ℂ) *
        polarRay ((P.figureCentralFan V c closes).heading i.castSucc) := by
  let A := P.figureCentralFan V c closes
  refine Fin.induction ?_ (fun k previous => ?_) i
  · change P.figureDevelopFrame V c closes (V.linkPolygon c 0) =
      (‖V.linkPolygon c 0‖ : ℂ) * polarRay (A.heading 0)
    rw [A.heading_zero, polarRay_zero, mul_one, P.figureDevelopFrame_agrees]
    exact P.figureCentralFrame_first V c closes 0
  · have successor := P.figureDevelopFrame_polar_successor V c closes k.castSucc
      (A.heading k.castSucc.castSucc) previous
    have rotated : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
    change P.figureDevelopFrame V c closes (V.linkPolygon c (finRotate (n + 1) k.castSucc)) =
      (‖V.linkPolygon c (finRotate (n + 1) k.castSucc)‖ : ℂ) *
        polarRay (A.heading k.castSucc.castSucc + A.angle k.castSucc) at successor
    rw [rotated, ← A.heading_succ, Fin.succ_castSucc] at successor
    exact successor

theorem figureDevelopFrame_heading_finish
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    P.figureDevelopFrame V c closes (V.linkPolygon c (finRotate (n + 1) i)) =
      (‖V.linkPolygon c (finRotate (n + 1) i)‖ : ℂ) *
        polarRay ((P.figureCentralFan V c closes).heading i.succ) := by
  have successor := P.figureDevelopFrame_polar_successor V c closes i _
    (P.figureDevelopFrame_heading V c closes i)
  rwa [← (P.figureCentralFan V c closes).heading_succ] at successor

theorem figureCentralFan_outer_ray
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    polarRay (P.figureCentralFan V c closes).totalAngle = 1 := by
  have terminal := P.figureDevelopFrame_heading_finish V c closes (Fin.last n)
  rw [finRotate_last, show (Fin.last n).succ = Fin.last (n + 1) from rfl,
    (P.figureCentralFan V c closes).heading_last,
    P.figureDevelopFrame_agrees, P.figureCentralFrame_first] at terminal
  have nonzero : (‖V.linkPolygon c 0‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (P.linkPolygon_ne_zero V c 0))
  have equal : (‖V.linkPolygon c 0‖ : ℂ) * polarRay (P.figureCentralFan V c closes).totalAngle =
      (‖V.linkPolygon c 0‖ : ℂ) * 1 := by simpa only [mul_one] using terminal.symm
  exact mul_left_cancel₀ nonzero equal

end Unfoldings.SpatialFolding.ConvexBoundary
