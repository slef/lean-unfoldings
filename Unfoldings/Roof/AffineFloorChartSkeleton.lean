module

public import Unfoldings.Roof.AffineFloorChartContacts
public import Unfoldings.Geometry.FiniteSegmentGerm
public import Unfoldings.Geometry.TriangleFrontier
public import Unfoldings.Geometry.SegmentEquation

/-! Coarse faces and genuine edges supply the endpoint creases and the flat connector bend. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

open Filter Topology

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} (T : FloorMesh family floor extra Z)
  (E : Plane ≃ₗᵢ[ℝ] Plane)

/-- A coarse corner read in the bank's horizontal chart. -/
def chartCorner (i : T.Index × Fin 3) : Plane := E ((T.projectedTriangle i.1).vertex i.2)

def chartEdgeEquation (i : T.Index × Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  segmentEquation (T.chartCorner E i) (T.chartCorner E (i.1, Triangle.next i.2))

theorem chartEdgeEquation_ne_zero (i : T.Index × Fin 3) : T.chartEdgeEquation E i ≠ 0 :=
  segmentEquation_ne_zero _ _

/-- Every generic point on the footprint belongs to the interior of a coarse face. -/
theorem exists_original_interior_of_chart_regular {q : Plane} (member : E.symm q ∈ clipAbove family floor Z)
    (regular : ∀ i, T.chartEdgeEquation E i q ≠ 0) :
    ∃ i, E.symm q ∈ interior (T.projectedTriangle i).carrier := by
  obtain ⟨i, face⟩ := Set.mem_iUnion.mp (T.cover.subset member)
  refine ⟨i, ?_⟩
  by_contra outside
  have boundary : E.symm q ∈ frontier (T.projectedTriangle i).carrier :=
    ⟨subset_closure face, outside⟩
  rw [(T.projectedTriangle i).frontier_eq_union_edges] at boundary
  obtain ⟨j, on_edge⟩ := Set.mem_iUnion.mp boundary
  apply regular (i, j)
  apply segmentEquation_eq_zero
  let U := E.toLinearEquiv.toAffineEquiv.toAffineMap
  have moved : U (E.symm q) ∈ U '' segment ℝ ((T.projectedTriangle i).vertex j)
      ((T.projectedTriangle i).vertex (Triangle.next j)) := ⟨E.symm q, on_edge, rfl⟩
  rw [image_segment ℝ] at moved
  have equal : U (E.symm q) = q := E.apply_symm_apply q
  change q ∈ segment ℝ (U ((T.projectedTriangle i).vertex j))
    (U ((T.projectedTriangle i).vertex (Triangle.next j)))
  rwa [equal] at moved

namespace LineRefinement

variable {T} {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)
  (inside : (interior (clipAbove family floor Z)).Nonempty)

local instance chartSkeletonIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

local notation "Q" => ConvexRoof.reorient (L.mesh.roof inside) E

/-- A trimmed endpoint ray on the coarse skeleton is tangent to its actual support crease. -/
theorem exists_tangentSlopes_of_chart_ray (w : L.mesh.pairedComplex.Vertex Set.univ) (d : Plane)
    (regular : ∀ i, (Q).projectedVertex w ≠ T.chartCorner E i)
    (follows : ∀ᶠ t : ℝ in 𝓝[>] 0, (Q).projectedVertex w + t • d ∈
      ⋃ i : T.Index × Fin 3, segment ℝ (T.chartCorner E i)
        (T.chartCorner E (i.1, Triangle.next i.2))) :
    ∃ a b : Plane,
      (∀ f j, L.mesh.pairedComplex.vertexOfCorner Set.univ (f, j) = w →
        (Q).normalSlope f = a ∨ (Q).normalSlope f = b) ∧ inner ℝ (a - b) d = 0 := by
  let : Finite T.Index := T.finite
  obtain ⟨⟨i, j⟩, on_edge, r, direction⟩ :=
    exists_incident_segment_of_ray_germ (T.chartCorner E)
      (fun i => T.chartCorner E (i.1, Triangle.next i.2)) ((Q).projectedVertex w) d follows
  obtain ⟨a, b, slopes, tied⟩ :=
    L.exists_tangentSlopes_of_chart_edge inside E w i j on_edge (fun k => regular (i, k))
  refine ⟨a, b, slopes, ?_⟩
  rw [direction, real_inner_smul_right]
  change r * inner ℝ (a - b) (E ((T.projectedTriangle i).vertex (Triangle.next j)) -
    E ((T.projectedTriangle i).vertex j)) = 0
  rw [tied, mul_zero]

end LineRefinement
end Unfoldings.SpatialEnvelope.FloorMesh
