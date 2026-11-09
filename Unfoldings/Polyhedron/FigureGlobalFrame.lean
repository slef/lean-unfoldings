module

public import Unfoldings.Polyhedron.FigureFrames
public import Unfoldings.Geometry.ComplexArea

/-!
# One normalized complex frame for the whole actual figure polygon

Normalize the first central triangle. Global consistency of the actual
signed areas then puts every successive pair in positive complex angular
order in this same frame, without reducing cumulative headings modulo a turn.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

include P

theorem linkPolygon_ne_zero (i : Fin (n + 1)) : V.linkPolygon c i ≠ 0 := by
  intro zero
  have boundary := P.figure_germPoint_mem_frontier V (c.point i)
  have outside : V.linkPolygon c i ∉ interior V.carrier := boundary.2
  rw [zero] at outside
  exact outside V.zero_mem_interior

theorem figureCentralFrame_cross_positive
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    0 < (starRingEnd ℂ ((P.figureCentralFrame V c closes 0).place (V.linkPolygon c i)) *
      (P.figureCentralFrame V c closes 0).place
        (V.linkPolygon c (finRotate (n + 1) i))).im := by
  let frame := P.figureCentralFrame V c closes 0
  let f : Plane ≃ᵃⁱ[ℝ] Plane := frame.place.trans
    Complex.orthonormalBasisOneI.repr.toAffineIsometryEquiv
  have zero : f 0 = 0 := by
    change Complex.orthonormalBasisOneI.repr (frame.place 0) = 0
    rw [P.figureCentralFrame_zero]
    exact map_zero _
  have initial : 0 < orient (f (V.linkPolygon c 0))
      (f (V.linkPolygon c (finRotate (n + 1) 0))) (f 0) := by
    rw [zero, orient_cyclic (0 : Plane)]
    change 0 < orient 0 (Complex.orthonormalBasisOneI.repr (frame.place (V.linkPolygon c 0)))
      (Complex.orthonormalBasisOneI.repr (frame.place (V.linkPolygon c (finRotate (n + 1) 0))))
    rw [orient_complex_repr_zero, P.figureCentralFrame_first]
    simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_pos (norm_pos_iff.mpr (P.linkPolygon_ne_zero V c 0)) frame.upper
  have mapped := orient_mul_pos_map f (P.linkPolygon_orient_product V c closes 0 i)
  have positive := (pos_iff_pos_of_mul_pos mapped).mp initial
  rw [zero, orient_cyclic (0 : Plane)] at positive
  change 0 < orient 0 (Complex.orthonormalBasisOneI.repr (frame.place (V.linkPolygon c i)))
    (Complex.orthonormalBasisOneI.repr (frame.place (V.linkPolygon c (finRotate (n + 1) i))))
    at positive
  rwa [orient_complex_repr_zero] at positive

end Unfoldings.SpatialFolding.ConvexBoundary
