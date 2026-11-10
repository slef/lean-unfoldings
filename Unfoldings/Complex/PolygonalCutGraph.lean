module

public import Unfoldings.Complex.PolygonalCuts

/-!
# Actual embedded polygonal forests on the original cut surface

Each new refined seam is an embedded arc in one original triangular face.
The vertex set also includes old boundary roots, as harmless isolated vertices
when no new cut meets them. Forests are proved for these actual embedded arcs.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision.CutPresentation

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {S : C.Subdivision D} {base : Set C.Seam} (P : S.CutPresentation base)
  (F : SpatialFolding C) (H : S.Conforming Set.univ Set.univ)

abbrev CutVertex := {v : D.Vertex P.uncut // v ∈ (D.relativeCutGraph P.retain P.uncut).vertexSet}

/-- The new cut arcs embedded in the original metric surface, including their boundary roots. -/
def embeddedGraph : FiniteEmbeddedGraph P.CutVertex (D.RelativeCutSeam P.retain P.uncut)
    (C.Realization base) where
  finite_vertices := inferInstance
  finite_edges := inferInstance
  vertex v := P.conforms.metricEquiv (D.vertexPoint P.uncut v.val)
  vertex_injective := P.conforms.metricEquiv.injective.comp
    ((D.vertexPoint_injective P.uncut).comp Subtype.val_injective)
  left s := ⟨D.relativeCutVertex P.retain P.uncut s false, Or.inr ⟨s, false, rfl⟩⟩
  right s := ⟨D.relativeCutVertex P.retain P.uncut s true, Or.inr ⟨s, true, rfl⟩⟩
  edge s := (⟨P.conforms.metricEquiv, P.conforms.metricEquiv.continuous⟩ :
    C(D.Realization P.uncut, C.Realization base)).comp (D.relativeSeamMap P.inclusion s)
  edge_zero s := congrArg P.conforms.metricEquiv (D.relativeSeamMap_zero P.inclusion s)
  edge_one s := congrArg P.conforms.metricEquiv (D.relativeSeamMap_one P.inclusion s)
  edge_injective s := by
    intro t _ht z _hz equal
    exact (F.subdivide S H).relativeSeamMap_injective P.inclusion s
      (P.conforms.metricEquiv.injective equal)
  edge_avoids_vertices s t positive less v equal :=
    D.relativeSeamMap_avoids_vertices P.inclusion s t positive less
      ⟨v.val, (P.conforms.metricEquiv.injective equal).symm⟩
  disjoint_open_edges s r different := by
    apply Set.disjoint_left.mpr
    rintro p ⟨t, ht, rfl⟩ ⟨z, _hz, equal⟩
    exact D.relativeSeamMap_ne_of_ne P.inclusion different t z ht.1 ht.2
      (P.conforms.metricEquiv.injective equal.symm)

/-- Forests in the presentation are forests of actual embedded polygonal arcs. -/
theorem embeddedGraph_acyclic (forest : P.IsRootedForest) :
    (P.embeddedGraph F H).graph.IsAcyclic := by
  apply forest.1.of_mapAlong (G := (P.embeddedGraph F H).graph)
    (H := D.relativeCutGraph P.retain P.uncut) Subtype.val (fun s => s)
    (fun v _ => v.property) _ Function.injective_id
  intro edge u v link
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Every arc is the projection of one actual bank of a newly removed refined seam. -/
theorem embeddedGraph_edge (s : D.RelativeCutSeam P.retain P.uncut) (t : unitInterval) :
    (P.embeddedGraph F H).edge s t =
      P.projection (D.bankMap P.retain (D.relativeCutBank P.retain P.uncut s false)
        (D.bankParameter P.retain (D.relativeCutBank P.retain P.uncut s false) t)) := rfl

/-- Each refined arc lies in one original face with its actual rigid parent coordinates. -/
theorem embeddedGraph_edge_parent (s : D.RelativeCutSeam P.retain P.uncut) (t : unitInterval) :
    (P.embeddedGraph F H).edge s t =
      C.faceMap base (S.parent (D.left s.val).face)
        (S.parentCell (D.left s.val).face
          ((D.triangle (D.left s.val).face).edgeMap (D.left s.val).edge
            (D.bankParameter P.retain (D.relativeCutBank P.retain P.uncut s false) t))) := rfl

end Unfoldings.TriangleComplex.Subdivision.CutPresentation
