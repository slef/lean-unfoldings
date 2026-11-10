module

public import Unfoldings.Complex.RelativeSeamGeometry
public import Unfoldings.Topology.GraphAcyclic
public import Unfoldings.Topology.GraphVertexMap

/-!
# The actual relative cut graph after collapsing the old boundary

Vertex labels are their actual image points, so the collapsed boundary is one
vertex. Each newly removed seam remains one named edge. Loops and parallel
edges survive, including an edge joining two original boundary roots.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v w

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} {X : Type w} [TopologicalSpace X]

def collapsedCutVertices (small large : Set C.Seam) (q : C(C.Realization large, X)) : Set X :=
  (fun v => q (C.vertexPoint large v)) '' (C.relativeCutGraph small large).vertexSet

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {small large : Set C.Seam} (inclusion : small ⊆ large) {X : Type w} [TopologicalSpace X]
  (q : C(C.Realization large, X))
  (fibers : ∀ x y, q x = q y ↔ x = y ∨ (x ∈ C.bankBoundary large ∧ y ∈ C.bankBoundary large))

def collapsedCutGraph :
    FiniteEmbeddedGraph (C.collapsedCutVertices small large q)
      (C.RelativeCutSeam small large) X where
  finite_vertices := Set.finite_coe_iff.mpr
    ((Set.toFinite (C.relativeCutGraph small large).vertexSet).image
      (fun v => q (C.vertexPoint large v)))
  finite_edges := inferInstance
  vertex := Subtype.val
  vertex_injective := Subtype.val_injective
  left s := ⟨q (C.vertexPoint large (C.relativeCutVertex small large s false)),
    _, Or.inr ⟨s, false, rfl⟩, rfl⟩
  right s := ⟨q (C.vertexPoint large (C.relativeCutVertex small large s true)),
    _, Or.inr ⟨s, true, rfl⟩, rfl⟩
  edge s := q.comp (C.relativeSeamMap inclusion s)
  edge_zero s := congrArg q (C.relativeSeamMap_zero inclusion s)
  edge_one s := congrArg q (C.relativeSeamMap_one inclusion s)
  edge_injective s := by
    intro t ht z _hz equal
    rcases (fibers _ _).mp equal with same | both
    · exact F.relativeSeamMap_injective inclusion s same
    · exact (C.relativeSeamMap_avoids_boundary inclusion s t ht.1 ht.2 both.1).elim
  edge_avoids_vertices s t positive less vertex := by
    obtain ⟨v, _member, equal⟩ := vertex.property
    intro same
    rcases (fibers _ _).mp (same.trans equal.symm) with same | both
    · exact C.relativeSeamMap_avoids_vertices inclusion s t positive less ⟨v, same.symm⟩
    · exact C.relativeSeamMap_avoids_boundary inclusion s t positive less both.1
  disjoint_open_edges s r different := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨z, _hz, equal⟩
    rcases (fibers _ _).mp equal.symm with same | both
    · exact C.relativeSeamMap_ne_of_ne inclusion different t z ht.1 ht.2 same
    · exact C.relativeSeamMap_avoids_boundary inclusion s t ht.1 ht.2 both.1

end Unfoldings.SpatialFolding
