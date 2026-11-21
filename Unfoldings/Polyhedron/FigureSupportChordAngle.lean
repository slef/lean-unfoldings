module

public import Unfoldings.Polyhedron.FigurePolygon
public import Unfoldings.Polyhedron.FigureSimpleChain
public import Unfoldings.Polyhedron.GermDirections
public import Unfoldings.Polyhedron.SupportingNormals
public import Unfoldings.Geometry.SegmentCoverFirstEdge
public import Unfoldings.Geometry.PositiveSpanAngle

/-! A straight boundary chord of the vertex figure spans at least one original corner angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {a : C.Vertex Set.univ} (V : F.VertexFigure a)
  {n : ℕ} (c : (C.linkSystem Set.univ a).Chain n)

include P in
/-- A straight figure boundary chord between distinct original link rays
subtends at least the minimum original face angle. -/
theorem min_angle_le_of_figure_boundary_chord
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (covers : ∀ p, c.Visited p)
    {eta : ℝ} (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i)
    (i j : Fin (n + 1)) (distinct : V.linkPolygon c i ≠ V.linkPolygon c j)
    (boundary : segment ℝ (V.linkPolygon c i) (V.linkPolygon c j) ⊆ frontier V.carrier) :
    eta ≤ EuclideanGeometry.angle (V.place (V.linkPolygon c i))
      (F.toSpace Set.univ (C.vertexPoint Set.univ a)) (V.place (V.linkPolygon c j)) := by
  let p := V.linkPolygon c
  let next := finRotate (n + 1)
  let x := p i
  let y := p j
  let apex := F.toSpace Set.univ (C.vertexPoint Set.univ a)
  have apart := V.linkPolygon_disjoint_open_edges c P.embedded closes
  have avoids_open (k l : Fin (n + 1)) : p k ∉ openSegment ℝ (p l) (p (next l)) := by
    intro on_edge
    by_cases equal : l = k
    · subst l
      exact V.linkPolygon_nondegenerate c closes k (left_mem_openSegment_iff.mp on_edge)
    · exact Set.disjoint_left.mp (apart l k equal) on_edge (left_mem_segment ℝ _ _)
  have cover : segment ℝ x y ⊆ ⋃ k, segment ℝ (p k) (p (next k)) := by
    have all_edges := P.linkPolygon_boundary V c closes covers
    change (⋃ k, (V.linkPolygon c).edgeSet ℝ k) = _ at all_edges
    simp_rw [V.linkPolygon_edgeSet c closes, V.germPoint_chain_rotates c closes] at all_edges
    change (⋃ k, segment ℝ (p k) (p (next k))) = frontier V.carrier at all_edges
    rwa [all_edges]
  have angle_mono (z : Plane) (hz : z ∈ segment ℝ x y) (z_ne : V.place z ≠ apex) :
      EuclideanGeometry.angle (V.place x) apex (V.place z) ≤
        EuclideanGeometry.angle (V.place x) apex (V.place y) := by
    obtain ⟨t, ht, rfl⟩ := segment_eq_image_lineMap ℝ x y ▸ hz
    have x_ne : V.place x ≠ apex := V.place_germPoint_ne_apex (c.point i)
    have placement : V.place (AffineMap.lineMap x y t) - apex =
        (1 - t) • (V.place x - apex) + t • (V.place y - apex) := by
      change V.place.toAffineMap (AffineMap.lineMap x y t) - apex = _
      rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
      change ((1 - t) • V.place x + t • V.place y) - _ = _
      simp only [smul_sub, sub_smul, one_smul]
      abel
    change angle (V.place x - apex) (V.place (AffineMap.lineMap x y t) - apex) ≤
      angle (V.place x - apex) (V.place y - apex)
    rw [placement]
    apply angle_le_of_nonnegative_combination (sub_ne_zero.mpr x_ne)
      (sub_nonneg.mpr ht.2) ht.1
    rw [← placement]
    exact sub_ne_zero.mpr z_ne
  obtain ⟨k, ⟨first, inside, _⟩ | ⟨last, inside, _⟩⟩ :=
    exists_first_edge_of_finite_segment_cover p (fun k => p (next k)) distinct cover
      (avoids_open i) (avoids_open j)
  · have small : eta ≤ EuclideanGeometry.angle (V.place (p k)) apex (V.place (p (next k))) := by
      change eta ≤ EuclideanGeometry.angle (V.place (V.germPoint (c.point k))) apex
        (V.place (V.germPoint (c.point (next k))))
      rw [← V.germPoint_chain_rotates c closes, V.germPoint_apex_angle]
      exact min_angle _ _
    rw [first] at small
    exact small.trans (angle_mono _ inside (V.place_germPoint_ne_apex (c.point (next k))))
  · have small : eta ≤ EuclideanGeometry.angle (V.place (p (next k))) apex (V.place (p k)) := by
      rw [EuclideanGeometry.angle_comm]
      change eta ≤ EuclideanGeometry.angle (V.place (V.germPoint (c.point k))) apex
        (V.place (V.germPoint (c.point (next k))))
      rw [← V.germPoint_chain_rotates c closes, V.germPoint_apex_angle]
      exact min_angle _ _
    rw [last] at small
    exact small.trans (angle_mono _ inside (V.place_germPoint_ne_apex (c.point k)))

include P V in
/-- Distinct original rays lying in a common supporting face plane bound an
angle at least as large as the minimum input corner angle. -/
theorem min_angle_le_of_link_rays_in_face_plane (N : F.SupportingNormals)
    (closes : C.linkMate Set.univ a (C.linkTurn Set.univ a c.last) = c.first)
    (covers : ∀ p, c.Visited p)
    {eta : ℝ} (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i)
    (i j : Fin (n + 1)) (different : i ≠ j) (f : Face)
    (incident : inner ℝ (N.normal f)
      (F.toSpace Set.univ (C.vertexPoint Set.univ a) - F.place f 0) = 0)
    (in_plane_i : inner ℝ (N.normal f) (F.germDirection (c.point i).val) = 0)
    (in_plane_j : inner ℝ (N.normal f) (F.germDirection (c.point j).val) = 0) :
    eta ≤ angle (F.germDirection (c.point i).val) (F.germDirection (c.point j).val) := by
  let apex := F.toSpace Set.univ (C.vertexPoint Set.univ a)
  let x := V.germPoint (c.point i)
  let y := V.germPoint (c.point j)
  have distinct : x ≠ y := fun h => different (V.germPoint_chain_injective c P.embedded closes h)
  have ray (p : C.LinkGerm Set.univ a) : F.germFarPoint p.val - apex = F.germDirection p.val := by
    unfold SpatialFolding.germDirection
    exact congrArg (fun z => F.germFarPoint p.val - z) (F.linkGerm_apex Set.univ a p).symm
  have at_plane (p : C.LinkGerm Set.univ a)
      (perp : inner ℝ (N.normal f) (F.germDirection p.val) = 0) :
      inner ℝ (N.normal f) (V.place (V.germPoint p) - F.place f 0) = 0 := by
    rw [V.place_germPoint, radialSlicePoint, AffineMap.lineMap_apply_module']
    change inner ℝ (N.normal f)
      ((V.level / V.functional (F.germFarPoint p.val - apex)) • (F.germFarPoint p.val - apex) +
        apex - F.place f 0) = 0
    rw [add_sub_assoc, inner_add_right, real_inner_smul_right, ray p, perp, incident]
    ring
  have boundary : segment ℝ x y ⊆ frontier V.carrier := by
    intro z hz
    have x_in : x ∈ V.carrier := by
      rw [V.carrier_eq_convexHull]
      exact subset_convexHull ℝ _ (V.germPoint_mem_generators (c.point i))
    have y_in : y ∈ V.carrier := by
      rw [V.carrier_eq_convexHull]
      exact subset_convexHull ℝ _ (V.germPoint_mem_generators (c.point j))
    have in_body : z ∈ V.carrier := V.convex_carrier.segment_subset x_in y_in hz
    apply (P.figure_frontier_iff_surface V z).mpr
    rw [P.boundary]
    refine ⟨subset_closure in_body, ?_⟩
    intro inside
    have strict := N.supporting_strict f inside
    obtain ⟨t, _, rfl⟩ := segment_eq_image_lineMap ℝ x y ▸ hz
    have plane_x := at_plane (c.point i) in_plane_i
    have plane_y := at_plane (c.point j) in_plane_j
    change inner ℝ (N.normal f) (V.place x - F.place f 0) = 0 at plane_x
    change inner ℝ (N.normal f) (V.place y - F.place f 0) = 0 at plane_y
    change inner ℝ (N.normal f) (V.place.toAffineMap (AffineMap.lineMap x y t) - F.place f 0) < 0
      at strict
    have difference :
        V.place.toAffineMap (AffineMap.lineMap x y t) - F.place f 0 =
          (1 - t) • (V.place x - F.place f 0) + t • (V.place y - F.place f 0) := by
      rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
      change ((1 - t) • V.place x + t • V.place y) - _ = _
      simp only [smul_sub, sub_smul, one_smul]
      abel
    rw [difference, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      plane_x, plane_y, mul_zero, mul_zero, add_zero] at strict
    exact (lt_irrefl (0 : ℝ)) strict
  have lower := P.min_angle_le_of_figure_boundary_chord V c closes covers min_angle i j
    distinct boundary
  have left_pos := V.positive.trans (V.supported (C.germFarCorner (c.point i).val)
    (F.linkGerm_far_ne_apex Set.univ a (c.point i)))
  have right_pos := V.positive.trans (V.supported (C.germFarCorner (c.point j).val)
    (F.linkGerm_far_ne_apex Set.univ a (c.point j)))
  rw [show V.linkPolygon c i = x from rfl, show V.linkPolygon c j = y from rfl,
    show V.place x = _ from V.place_germPoint (c.point i),
    show V.place y = _ from V.place_germPoint (c.point j)] at lower
  have normalized := angle_radialSlicePoint V.functional apex (F.germFarPoint (c.point i).val)
    (F.germFarPoint (c.point j).val) V.level V.positive left_pos right_pos
  change eta ≤ EuclideanGeometry.angle
    (radialSlicePoint V.functional apex V.level (F.germFarPoint (c.point i).val)) apex
    (radialSlicePoint V.functional apex V.level (F.germFarPoint (c.point j).val)) at lower
  rw [normalized] at lower
  change eta ≤ angle (F.germFarPoint (c.point i).val - apex)
    (F.germFarPoint (c.point j).val - apex) at lower
  rwa [ray (c.point i), ray (c.point j)] at lower

end Unfoldings.SpatialFolding.ConvexBoundary
