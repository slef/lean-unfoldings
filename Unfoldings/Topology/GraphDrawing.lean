module

public import Unfoldings.Topology.FiniteEmbeddedGraph
public import Unfoldings.Topology.GraphVertexMap
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Topology.Path
public import Schoenflies.Graph.CycleJordan

/-!
# Finite embedded graphs as actual plane drawings

Relabel abstract vertices by their embedded plane points and extend each edge
parametrization constantly beyond the unit interval. For nonloop edges this
satisfies the precise drawing interface used by the pinned Jordan–Schönflies
library. This bridge preserves the actual edge sets and parametrizations.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge : Type*} (G : FiniteEmbeddedGraph Vertex Edge Schoenflies.Plane)

def planeGraph : Graph Schoenflies.Plane Edge := G.graph.map G.vertex

def edgePath (e : Edge) : Path (G.vertex (G.left e)) (G.vertex (G.right e)) where
  toContinuousMap := G.edge e
  source' := G.edge_zero e
  target' := G.edge_one e

def drawing (e : Edge) : ℝ → Schoenflies.Plane := (G.edgePath e).extend

theorem drawing_apply (e : Edge) {t : ℝ} (inside : t ∈ Set.Icc (0 : ℝ) 1) :
    G.drawing e t = G.edge e ⟨t, inside⟩ := (G.edgePath e).extend_apply inside

theorem drawing_edgeArc (e : Edge) : Graph.edgeArc G.drawing e = Set.range (G.edge e) := by
  exact (G.edgePath e).image_extend_of_subset (Set.Subset.refl _)

theorem planeGraph_vertexSet : G.planeGraph.vertexSet = Set.range G.vertex := by
  change G.vertex '' Set.univ = Set.range G.vertex
  exact Set.image_univ

theorem planeGraph_isLink (e : Edge) :
    G.planeGraph.IsLink e (G.vertex (G.left e)) (G.vertex (G.right e)) :=
  Graph.IsLink.map G.vertex (show G.graph.IsLink e (G.left e) (G.right e)
    from Or.inl ⟨rfl, rfl⟩)

/-- The project's abstract embedded-graph interface supplies a genuine plane drawing. -/
theorem isDrawing (edge_injective : ∀ e, Function.Injective (G.edge e)) :
    Graph.IsDrawing G.planeGraph G.drawing := by
  have vertex_arc {e : Edge} {x y p : Schoenflies.Plane}
      (link : G.planeGraph.IsLink e x y) (vertex : p ∈ G.planeGraph.vertexSet)
      (inside : p ∈ Graph.edgeArc G.drawing e) : p = x ∨ p = y := by
    rw [G.planeGraph_vertexSet] at vertex
    obtain ⟨v, rfl⟩ := vertex
    rw [G.drawing_edgeArc] at inside
    obtain ⟨t, equal⟩ := inside
    by_cases zero : t = 0
    · have point : G.vertex v = G.vertex (G.left e) := by
        rw [zero, G.edge_zero] at equal
        exact equal.symm
      rw [point]
      exact (G.planeGraph_isLink e).inc_left.eq_or_eq_of_isLink link
    by_cases one : t = 1
    · have point : G.vertex v = G.vertex (G.right e) := by
        rw [one, G.edge_one] at equal
        exact equal.symm
      rw [point]
      exact (G.planeGraph_isLink e).inc_right.eq_or_eq_of_isLink link
    · exact (G.edge_avoids_vertices e t (bot_lt_iff_ne_bot.mpr zero)
        (lt_top_iff_ne_top.mpr one) v equal).elim
  refine ⟨?_, @vertex_arc, ?_⟩
  · intro e _he
    refine ⟨(G.edgePath e).continuous_extend.continuousOn, ?_, ?_⟩
    · intro s hs t ht equal
      rw [G.drawing_apply e hs, G.drawing_apply e ht] at equal
      exact congrArg (fun p : unitInterval => p.val) (edge_injective e equal)
    · change G.planeGraph.IsLink e ((G.edgePath e).extend 0) ((G.edgePath e).extend 1)
      rw [Path.extend_zero, Path.extend_one]
      exact G.planeGraph_isLink e
  · intro e f _he _hf different p he hf
    rw [G.drawing_edgeArc] at he hf
    obtain ⟨s, equal_s⟩ := he
    obtain ⟨t, equal_t⟩ := hf
    have is_vertex : p ∈ G.planeGraph.vertexSet := by
      by_contra outside
      have s_zero : s ≠ 0 := by
        intro zero
        apply outside
        rw [← equal_s, zero, G.edge_zero]
        exact (G.planeGraph_isLink e).left_mem
      have s_one : s ≠ 1 := by
        intro one
        apply outside
        rw [← equal_s, one, G.edge_one]
        exact (G.planeGraph_isLink e).right_mem
      have t_zero : t ≠ 0 := by
        intro zero
        apply outside
        rw [← equal_t, zero, G.edge_zero]
        exact (G.planeGraph_isLink f).left_mem
      have t_one : t ≠ 1 := by
        intro one
        apply outside
        rw [← equal_t, one, G.edge_one]
        exact (G.planeGraph_isLink f).right_mem
      exact Set.disjoint_left.mp (G.disjoint_open_edges e f different)
        ⟨s, ⟨bot_lt_iff_ne_bot.mpr s_zero, lt_top_iff_ne_top.mpr s_one⟩, equal_s⟩
        ⟨t, ⟨bot_lt_iff_ne_bot.mpr t_zero, lt_top_iff_ne_top.mpr t_one⟩, equal_t⟩
    have on_e : p ∈ Graph.edgeArc G.drawing e := by rw [G.drawing_edgeArc]; exact ⟨s, equal_s⟩
    have on_f : p ∈ Graph.edgeArc G.drawing f := by rw [G.drawing_edgeArc]; exact ⟨t, equal_t⟩
    refine ⟨is_vertex, ?_, ?_⟩
    · rcases vertex_arc (G.planeGraph_isLink e) is_vertex on_e with rfl | rfl
      · exact (G.planeGraph_isLink e).inc_left
      · exact (G.planeGraph_isLink e).inc_right
    · rcases vertex_arc (G.planeGraph_isLink f) is_vertex on_f with rfl | rfl
      · exact (G.planeGraph_isLink f).inc_left
      · exact (G.planeGraph_isLink f).inc_right

/-- The actual carrier of any embedded nonloop graph cycle is a Jordan curve. -/
theorem cycle_isJordanCurve (edge_injective : ∀ e, Function.Injective (G.edge e))
    {e : Edge} {u v : Vertex} {detour : List Edge} (cycle : G.graph.IsCycleThrough e u v detour) :
    Schoenflies.IsJordanCurve (Graph.edgesCover G.drawing (e :: detour)) :=
  (G.isDrawing edge_injective).cycle_isJordanCurve
    (cycle.mapVertices G.vertex G.vertex_injective)

end Unfoldings.FiniteEmbeddedGraph
