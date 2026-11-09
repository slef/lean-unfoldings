module

public import Unfoldings.Polyhedron.FigureSimpleChain
public import Unfoldings.Polyhedron.FigureEdgeInteriors
public import Unfoldings.Polyhedron.FigureGermAngles
public import Unfoldings.Geometry.PolygonEdges
public import Unfoldings.Geometry.TransversePyramid

/-!
# The actual simple vertex-figure polygon

The vertices and edges come from the derived surface link. Cyclic pairing
supplies the successor, embeddedness excludes all open-edge contacts, and
the actual incident sections give exact boundary coverage. No polygon
angle-sum or curvature bound is assumed in this construction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.VertexFigure

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

def linkPolygon : Polygon Plane (n + 1) := ⟨fun i => V.germPoint (c.point i)⟩

theorem germPoint_chain_rotates
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    V.germPoint (C.linkTurn Set.univ v (c.point i)) =
      V.germPoint (c.point (finRotate (n + 1) i)) := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [finRotate_last]
    exact V.germPoint_chain_closes c closes
  · have rotated : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
    rw [rotated]
    exact V.germPoint_chain_next c k

theorem linkPolygon_nondegenerate
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    (V.linkPolygon c).HasNondegenerateEdges := by
  intro i
  change V.germPoint (c.point i) ≠ V.germPoint (c.point (finRotate (n + 1) i))
  rw [← V.germPoint_chain_rotates c closes i]
  exact V.germPoint_ne_turn (c.point i)

theorem linkPolygon_edgeSet
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (i : Fin (n + 1)) :
    (V.linkPolygon c).edgeSet ℝ i = segment ℝ (V.germPoint (c.point i))
      (V.germPoint (C.linkTurn Set.univ v (c.point i))) := by
  change affineSegment ℝ _ _ = _
  rw [affineSegment_eq_segment]
  change segment ℝ (V.germPoint (c.point i))
    (V.germPoint (c.point (finRotate (n + 1) i))) = _
  rw [V.germPoint_chain_rotates c closes i]

theorem linkPolygon_disjoint_open_edges (embedded : F.IsEmbedded)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    (V.linkPolygon c).HasDisjointOpenEdges := by
  intro i j different
  change Disjoint (openSegment ℝ (V.germPoint (c.point i))
    (V.germPoint (c.point (finRotate (n + 1) i))))
    (segment ℝ (V.germPoint (c.point j))
      (V.germPoint (c.point (finRotate (n + 1) j))))
  rw [← V.germPoint_chain_rotates c closes i, ← V.germPoint_chain_rotates c closes j]
  apply V.germ_openSegment_disjoint_segment embedded
  intro corners
  rcases (C.germ_corner_eq_iff _ _).mp corners with same | opposite
  · exact different (c.injective (Subtype.ext same))
  · exact c.disjoint i j (Subtype.ext opposite)

include V in
theorem linkPolygon_three_le (embedded : F.IsEmbedded)
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first) :
    3 ≤ n + 1 :=
  (V.linkPolygon_disjoint_open_edges c embedded closes).three_le
    (V.linkPolygon_nondegenerate c closes)

theorem linkPolygon_sum_apexAngle
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    (∑ i, EuclideanGeometry.angle (V.place (V.linkPolygon c i))
      (F.toSpace Set.univ (C.vertexPoint Set.univ v))
      (V.place (V.linkPolygon c (finRotate (n + 1) i)))) = C.totalAngle Set.univ v := by
  calc
    _ = ∑ i : Fin (n + 1), (C.triangle (c.point i).val.1.1).cornerAngle
        (c.point i).val.1.2 := by
      apply Finset.sum_congr rfl
      intro i _
      change EuclideanGeometry.angle (V.place (V.germPoint (c.point i))) _
        (V.place (V.germPoint (c.point (finRotate (n + 1) i)))) = _
      rw [← V.germPoint_chain_rotates c closes i]
      exact V.germPoint_apex_angle (c.point i)
    _ = _ := C.sum_linkCornerAngle Set.univ v c covers

theorem linkPolygon_angle_budget
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    C.totalAngle Set.univ v +
      (∑ i, EuclideanGeometry.angle (V.linkPolygon c ((finRotate (n + 1)).symm i))
        (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i))) ≤
      (n + 1 : ℝ) * Real.pi := by
  have budget := pyramid_angle_budget (finRotate (n + 1))
    (F.toSpace Set.univ (C.vertexPoint Set.univ v))
    (fun i => V.place (V.linkPolygon c i))
    (fun i => V.place_germPoint_ne_apex (c.point i))
  rw [V.linkPolygon_sum_apexAngle c closes covers] at budget
  simpa only [V.place.angle_map, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using budget

theorem linkPolygon_strict_angle_budget
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    C.totalAngle Set.univ v +
      (∑ i, EuclideanGeometry.angle (V.linkPolygon c ((finRotate (n + 1)).symm i))
        (V.linkPolygon c i) (V.linkPolygon c (finRotate (n + 1) i))) <
      (n + 1 : ℝ) * Real.pi := by
  have budget := pyramid_angle_budget_strict_of_nonzero_level (finRotate (n + 1))
    (F.toSpace Set.univ (C.vertexPoint Set.univ v))
    (fun i => V.place (V.linkPolygon c i)) V.functional V.level V.positive.ne'
    (fun i => V.range_place.le ⟨V.linkPolygon c i, rfl⟩)
  rw [V.linkPolygon_sum_apexAngle c closes covers] at budget
  simpa only [V.place.angle_map, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using budget

end Unfoldings.SpatialFolding.VertexFigure

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)
  {v : C.Vertex Set.univ} (V : F.VertexFigure v)
  {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

include P

theorem linkPolygon_boundary
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) :
    (V.linkPolygon c).boundary ℝ = frontier V.carrier := by
  change (⋃ i, (V.linkPolygon c).edgeSet ℝ i) = _
  simp_rw [V.linkPolygon_edgeSet c closes]
  exact (P.figure_boundary_eq_chain V c covers).symm

end Unfoldings.SpatialFolding.ConvexBoundary
