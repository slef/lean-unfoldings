module

public import Unfoldings.Polyhedron.FaceSupport
public import Unfoldings.Geometry.FrontierProjection
public import Unfoldings.Geometry.Barycentric

/-!
# A convex boundary cannot end along an original triangle edge

Move across the triangle edge in its supporting plane, then project radially
from a body interior point back to the convex frontier. Projection cannot
land in the original triangle: its supporting level forces a point already
in that plane to be fixed. Thus other surface points occur arbitrarily near
every edge point, on the other side of its original closed triangle.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_surface_near_edge_outside_face (face : Face) (e : Fin 3)
    (x : (C.triangle face).Edge e) (ε : ℝ) (positive : 0 < ε) :
    ∃ z ∈ F.surface, dist z (F.place face x.val) < ε ∧ z ∉ F.faceImage face := by
  let T := C.triangle face
  obtain ⟨origin, inside⟩ := P.interior_nonempty
  obtain ⟨f, a, _nonzero, _supported, strict, level⟩ := P.exists_face_support face
  have below : f origin < a := strict origin inside
  let q (t : ℝ) := F.place face (AffineMap.lineMap x.val (T.opposite e) (-t))
  let z (t : ℝ) := frontierProjectionFrom F.vertexHull origin (q t)
  have at_level (t : ℝ) : f (q t) = a := level _
  have different (t : ℝ) : q t ≠ origin := by
    intro equal
    have height := at_level t
    rw [equal] at height
    exact below.ne height
  have initial_q : q 0 = F.place face x.val := by simp [q]
  have boundary : F.place face x.val ∈ frontier F.vertexHull := by
    rw [← P.boundary]
    exact Set.mem_iUnion.mpr ⟨face, x.val, T.edge_subset e x.property, rfl⟩
  have initial : z 0 = F.place face x.val := by
    change frontierProjectionFrom F.vertexHull origin (q 0) = _
    rw [initial_q]
    exact frontierProjectionFrom_eq_self F.convex_vertexHull inside boundary
  have on_surface (t : ℝ) : z t ∈ F.surface := by
    rw [P.boundary]
    exact frontierProjectionFrom_mem F.convex_vertexHull F.compact_vertexHull inside (different t)
  have outside (t : ℝ) (ht : 0 < t) : z t ∉ F.faceImage face := by
    rintro ⟨y, hy, image⟩
    have projected_level : f (z t) = a := by rw [← image]; exact level y
    have fixed : z t = q t := frontierProjectionFrom_eq_of_level origin (q t) f a below
      (at_level t) projected_level
    have coordinates : y = AffineMap.lineMap x.val (T.opposite e) (-t) :=
      (F.place face).injective (image.trans fixed)
    have nonnegative := T.carrier_eq_nonneg_coord.le hy (Triangle.next (Triangle.next e))
    rw [coordinates, (T.coord (Triangle.next (Triangle.next e))).apply_lineMap,
      T.coord_edge_eq_zero e x] at nonnegative
    have opposite_coordinate : T.coord (Triangle.next (Triangle.next e)) (T.opposite e) = 1 := by
      simp [Triangle.opposite]
    rw [opposite_coordinate] at nonnegative
    simp only [AffineMap.lineMap_apply_ring, mul_one] at nonnegative
    linarith
  have continuous_q : Continuous q := by
    apply (F.place face).continuous.comp
    change Continuous (fun t : ℝ => AffineMap.lineMap x.val (T.opposite e) (-t))
    fun_prop
  have continuous_z : ContinuousAt z 0 :=
    (continuousAt_frontierProjectionFrom F.convex_vertexHull F.compact_vertexHull
      inside (different 0)).comp continuous_q.continuousAt
  obtain ⟨δ, δpos, control⟩ := Metric.continuousAt_iff.mp continuous_z ε positive
  have parameter_positive : 0 < δ / 2 := by linarith
  have near : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos parameter_positive]
    linarith
  refine ⟨z (δ / 2), on_surface _, ?_, outside _ parameter_positive⟩
  have close := control near
  rwa [initial] at close

end Unfoldings.SpatialFolding.ConvexBoundary
