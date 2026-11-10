module

public import Unfoldings.Complex.BoundaryAtlas
public import Unfoldings.Complex.BoundaryJordan
public import Unfoldings.Polyhedron.Convex
public import Unfoldings.Topology.SphereChart

/-!
# Every nontrivial cut of a convex sphere has a planar embedding

The actual inward embedding separates all banks inside the uncut sphere. A
point on the cut graph lies outside that embedding; stereographic projection
from its sphere image gives a closed planar embedding of the entire cut
surface. The result does not assume a tree or disk topology.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem exists_planarCutEmbedding (retain : Set C.Seam)
    (cut : (C.bankBoundary retain).Nonempty) :
    ∃ f : C(C.Realization retain, Plane), Topology.IsClosedEmbedding f := by
  let inclusion : retain ⊆ (Set.univ : Set C.Seam) := Set.subset_univ _
  let Q := C.forgetCutsBoundaryQuotient inclusion
  obtain ⟨g, embedded, misses⟩ := F.exists_cutEmbedding inclusion
  obtain ⟨p, boundary⟩ := cut
  let pole := Q.projection p
  have pole_mem : pole ∈ Q.boundaryImage := ⟨p, boundary, rfl⟩
  have avoids (x : C.Realization retain) : g x ≠ pole := by
    intro same
    have absent := misses (Set.mem_range_self x)
    exact absent (same.symm ▸ pole_mem)
  let h := P.sphereHomeomorph
  let spherePole := h pole
  let into : C(C.Realization retain,
      ↥(({spherePole} : Set (Metric.sphere (0 : Space) 1))ᶜ)) :=
    ⟨fun x => ⟨h (g x), by
      change h (g x) ≠ spherePole
      exact fun same => avoids x (h.injective same)⟩,
      by fun_prop⟩
  have injective : Function.Injective into := by
    intro x y equal
    exact embedded.injective (h.injective (congrArg Subtype.val equal))
  let : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp [Space]⟩
  let chart := spherePunctureHomeomorph 2 spherePole
  let f : C(C.Realization retain, Plane) := ⟨chart ∘ into, chart.continuous.comp into.continuous⟩
  exact ⟨f, f.continuous.isClosedEmbedding (chart.injective.comp injective)⟩

theorem exists_planarBoundaryJordan (retain : Set C.Seam) (bank : C.BoundaryBank retain) :
    ∃ (f : C(C.Realization retain, Plane)) (embedded : Topology.IsClosedEmbedding f),
      ∃ (u v : C.BoundaryVertex retain) (detour : List (C.BoundaryBank retain)),
        (C.boundaryGraph retain).graph.IsCycleThrough bank u v detour ∧
          Schoenflies.IsJordanCurve (Graph.edgesCover
            ((C.boundaryGraph retain).mapEmbedding f embedded.injective).drawing
            (bank :: detour)) := by
  obtain ⟨x, _⟩ := (C.triangle bank.val.face).exists_edge_nonvertex bank.val.edge
  obtain ⟨f, embedded⟩ := P.exists_planarCutEmbedding retain
    ⟨C.bankMap retain bank x, C.bankMap_mem_bankBoundary retain bank x⟩
  refine ⟨f, embedded, ?_⟩
  exact F.exists_boundaryJordanThroughBank retain f embedded.injective bank

end Unfoldings.SpatialFolding.ConvexBoundary
