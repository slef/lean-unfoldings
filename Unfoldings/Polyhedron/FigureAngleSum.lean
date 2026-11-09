module

public import Unfoldings.Polyhedron.FigureFullTurn
public import Unfoldings.Geometry.BoundaryCornerAngle

/-!
# The actual figure polygon angle sum and strict extreme-vertex angle bound

The proved one-turn central fan and exact splitting of each boundary corner
give the planar polygon angle sum, including collinear subdivisions. The
strict lateral pyramid budget then bounds the genuine surface total angle.
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

theorem linkPolygon_corner_split
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    EuclideanGeometry.angle (V.linkPolygon c ((finRotate (n + 1)).symm i)) (V.linkPolygon c i)
        (V.linkPolygon c (finRotate (n + 1) i)) =
      EuclideanGeometry.angle (V.linkPolygon c ((finRotate (n + 1)).symm i)) (V.linkPolygon c i) 0 +
        EuclideanGeometry.angle 0 (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i)) := by
  let prev := (finRotate (n + 1)).symm i
  have next_prev : finRotate (n + 1) prev = i := (finRotate (n + 1)).apply_symm_apply i
  have ab : V.linkPolygon c prev ≠ V.linkPolygon c i := by
    simpa only [next_prev] using V.linkPolygon_nondegenerate c closes prev
  have different : prev ≠ i := fun same => ab (congrArg (V.linkPolygon c) same)
  have first := P.linkPolygon_edge_subset_frontier V c closes prev
  have left := V.linkPolygon_disjoint_open_edges c P.embedded closes prev i different
  have right := V.linkPolygon_disjoint_open_edges c P.embedded closes i prev different.symm
  rw [next_prev] at first left right
  exact angle_eq_add_of_adjacent_boundary_edges V.convex_carrier V.compact_carrier.isClosed
    V.zero_mem_interior ab (V.linkPolygon_nondegenerate c closes i) first
    (P.linkPolygon_edge_subset_frontier V c closes i) left right

theorem linkPolygon_angle_sum
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    (∑ i, EuclideanGeometry.angle (V.linkPolygon c ((finRotate (n + 1)).symm i))
      (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i))) =
      ((n + 1 : ℝ) - 2) * Real.pi := by
  classical
  let A := P.figureCentralFan V c closes
  let L (i : Fin (n + 1)) := EuclideanGeometry.angle 0 (V.linkPolygon c i)
    (V.linkPolygon c (finRotate (n + 1) i))
  let R (i : Fin (n + 1)) := EuclideanGeometry.angle (V.linkPolygon c i)
    (V.linkPolygon c (finRotate (n + 1) i)) 0
  have triangle (i : Fin (n + 1)) : A.angle i + L i + R i = Real.pi := by
    have sum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (V.linkPolygon c (finRotate (n + 1) i)) (P.linkPolygon_ne_zero V c i)
    change EuclideanGeometry.angle (V.linkPolygon c i) 0
      (V.linkPolygon c (finRotate (n + 1) i)) + L i + R i = _
    linarith [EuclideanGeometry.angle_comm (V.linkPolygon c i) 0
      (V.linkPolygon c (finRotate (n + 1) i))]
  have triangles : A.totalAngle + (∑ i, L i) + (∑ i, R i) = (n + 1 : ℝ) * Real.pi := by
    have equal := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => triangle i)
    simpa only [AngularFan.totalAngle, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using equal
  have corners : (∑ i, EuclideanGeometry.angle
      (V.linkPolygon c ((finRotate (n + 1)).symm i)) (V.linkPolygon c i)
      (V.linkPolygon c (finRotate (n + 1) i))) = (∑ i, R i) + (∑ i, L i) := by
    simp_rw [P.linkPolygon_corner_split V c closes]
    rw [Finset.sum_add_distrib]
    have previous : (∑ i, EuclideanGeometry.angle
        (V.linkPolygon c ((finRotate (n + 1)).symm i)) (V.linkPolygon c i) 0) = ∑ i, R i := by
      have reindex := (finRotate (n + 1)).symm.sum_comp R
      simpa only [R, Equiv.apply_symm_apply] using reindex
    rw [previous]
  rw [corners]
  have full := P.figureCentralFan_full_turn V c closes
  change A.totalAngle = 2 * Real.pi at full
  linarith

include P V in
theorem totalAngle_lt_two_pi_of_vertexFigure (interior : ¬ C.IsBoundaryVertex Set.univ v) :
    C.totalAngle Set.univ v < 2 * Real.pi := by
  obtain ⟨n, c, closes, covers⟩ := C.exists_cyclic_link Set.univ v interior
  have budget := V.linkPolygon_strict_angle_budget c closes covers
  rw [P.linkPolygon_angle_sum V c closes] at budget
  linarith

include P in
theorem totalAngle_lt_two_pi_of_extreme (v : C.Vertex Set.univ)
    (interior : ¬ C.IsBoundaryVertex Set.univ v)
    (extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∈ F.vertexHull.extremePoints ℝ) :
    C.totalAngle Set.univ v < 2 * Real.pi :=
  P.totalAngle_lt_two_pi_of_vertexFigure (P.vertexFigure v extreme) interior

end Unfoldings.SpatialFolding.ConvexBoundary
