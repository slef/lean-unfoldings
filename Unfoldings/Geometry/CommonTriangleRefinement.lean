module

public import Unfoldings.Geometry.CommonBoundarySubdivision
public import Unfoldings.Geometry.SubdividedBoundaryFan
public import Unfoldings.Geometry.TriangleFanBoundary

/-!
# Refining a whole finite triangle family using common boundary edge labels

All old boundaries are subdivided together. A center fan inside each old
triangle uses exactly the global boundary edges contained in that triangle's
frontier. The resulting triangles cover each old parent exactly and preserve
pairwise interior separation. Constructing the associated seam system is a
further step.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {I : Type*} [Finite I] (original : I → Triangle)

structure CommonTriangleRefinement where
  Vertex : Type
  Edge : Type
  graph : FiniteEmbeddedGraph Vertex Edge Plane
  straight : graph.IsStraight
  boundary_cover : ∀ i, ∀ x ∈ frontier (original i).carrier,
    (∃ v, graph.vertex v = x) ∨
      ∃ e, Set.range (graph.edge e) ⊆ frontier (original i).carrier ∧ x ∈ Set.range (graph.edge e)
  center : I → Plane
  center_inside : ∀ i, center i ∈ interior (original i).carrier

def commonTriangleRefinement : CommonTriangleRefinement original := Classical.choice (by
  obtain ⟨Vertex, Edge, G, straight, _carrier, cover⟩ :=
    exists_common_triangle_boundary_subdivision original
  exact ⟨⟨Vertex, Edge, G, straight, cover,
    fun i => (original i).interior_nonempty.choose,
    fun i => (original i).interior_nonempty.choose_spec⟩⟩)

namespace CommonTriangleRefinement

variable {original} (R : CommonTriangleRefinement original)

abbrev Index := (i : I) × R.graph.SubdividedBoundaryEdge (S := (original i).carrier)

instance finite_index : Finite R.Index := by
  let := R.graph.finite_edges
  classical
  infer_instance

def triangle (j : R.Index) : Triangle :=
  R.graph.subdividedBoundaryTriangle R.straight (original j.1).compact_carrier
    (original j.1).convex_carrier (R.center_inside j.1) j.2

omit [Finite I] in
theorem triangle_subset (j : R.Index) : (R.triangle j).carrier ⊆ (original j.1).carrier :=
  R.graph.subdividedBoundaryTriangle_subset R.straight (original j.1).compact_carrier
    (original j.1).convex_carrier (R.center_inside j.1) j.2

omit [Finite I] in
/-- Every old triangle is covered exactly by its own refined center fan. -/
theorem parent_cover (i : I) : (original i).carrier =
    ⋃ e : R.graph.SubdividedBoundaryEdge (S := (original i).carrier),
      (R.triangle ⟨i, e⟩).carrier :=
  R.graph.subdividedBoundaryTriangle_cover R.straight (original i).compact_carrier
    (original i).convex_carrier (R.center_inside i) (R.boundary_cover i)

omit [Finite I] in
theorem total_cover : (⋃ i, (original i).carrier) = ⋃ j : R.Index, (R.triangle j).carrier := by
  ext p
  constructor
  · intro member
    obtain ⟨i, parent⟩ := Set.mem_iUnion.mp member
    rw [R.parent_cover i] at parent
    obtain ⟨e, child⟩ := Set.mem_iUnion.mp parent
    exact Set.mem_iUnion.mpr ⟨⟨i, e⟩, child⟩
  · intro member
    obtain ⟨j, child⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨j.1, R.triangle_subset j child⟩

omit [Finite I] in
/-- Common refinement preserves the existing disjoint-interior partition. -/
theorem separated
    (separated : Pairwise (fun i j =>
      Disjoint (interior (original i).carrier) (interior (original j).carrier))) :
    Pairwise (fun j k : R.Index =>
      Disjoint (interior (R.triangle j).carrier) (interior (R.triangle k).carrier)) := by
  intro j k different
  by_cases parent_same : j.1 = k.1
  · obtain ⟨i, e⟩ := j
    obtain ⟨l, f⟩ := k
    change i = l at parent_same
    subst l
    exact R.graph.subdividedBoundaryTriangle_separated R.straight (original i).compact_carrier
      (original i).convex_carrier (R.center_inside i)
      (fun same => different (congrArg (Sigma.mk i) same))
  · exact (separated parent_same).mono (interior_mono (R.triangle_subset j))
      (interior_mono (R.triangle_subset k))

omit [Finite I] in
/-- Each refined base is exactly its globally named shared graph edge. -/
theorem base_edge (j : R.Index) : (R.triangle j).edge 1 = Set.range (R.graph.edge j.2.val) :=
  (R.straight.range_edge R.graph j.2.val).symm

omit [Finite I] in
/-- A refined triangle touches its old parent's frontier only at the global base edge. -/
theorem parent_frontier_subset_base (j : R.Index) :
    (R.triangle j).carrier ∩ frontier (original j.1).carrier ⊆
      Set.range (R.graph.edge j.2.val) := by
  rw [R.straight.range_edge R.graph j.2.val]
  exact (original j.1).fan_frontier_subset_base (R.center_inside j.1)
    (R.graph.vertex_injective.ne (R.straight.endpoints_ne j.2.val))
    (by rw [← R.straight.range_edge R.graph j.2.val]; exact j.2.property)

end CommonTriangleRefinement
end Unfoldings
