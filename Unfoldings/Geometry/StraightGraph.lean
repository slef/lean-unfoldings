module

public import Unfoldings.Topology.FiniteEmbeddedGraph
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Tactic.NormNum

/-! Embedded straight edges retain their affine formulas and form a simple graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {Vertex Edge E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (G : FiniteEmbeddedGraph Vertex Edge E)

def IsStraight : Prop := ∀ e t, G.edge e t =
  AffineMap.lineMap (G.vertex (G.left e)) (G.vertex (G.right e)) (t : ℝ)

variable {G}

theorem IsStraight.open_edge_image (straight : G.IsStraight) (e : Edge) :
    G.edge e '' Set.Ioo (0 : unitInterval) 1 =
      openSegment ℝ (G.vertex (G.left e)) (G.vertex (G.right e)) := by
  rw [openSegment_eq_image_lineMap]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.val, ht, (straight e t).symm⟩
  · rintro ⟨t, ht, equal⟩
    let time : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
    exact ⟨time, ht, (straight e time).trans equal⟩

theorem IsStraight.endpoints_ne (straight : G.IsStraight) (e : Edge) :
    G.left e ≠ G.right e := by
  let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have positive : 0 < t := by change (0 : ℝ) < 1 / 2; norm_num
  have before : t < 1 := by change (1 / 2 : ℝ) < 1; norm_num
  intro equal
  apply G.edge_avoids_vertices e t positive before (G.right e)
  rw [straight e t, equal, AffineMap.lineMap_same]
  rfl

theorem IsStraight.graph_simple (straight : G.IsStraight) : G.graph.Simple := by
  rw [Graph.simple_iff, Graph.loopless_iff]
  constructor
  · intro e v loop
    rcases loop with ⟨left, right⟩ | ⟨right, left⟩
    all_goals exact straight.endpoints_ne e (left.symm.trans right)
  · intro e f x y first second
    by_contra different
    have equal_images : G.edge e '' Set.Ioo (0 : unitInterval) 1 =
        G.edge f '' Set.Ioo (0 : unitInterval) 1 := by
      rw [straight.open_edge_image e, straight.open_edge_image f]
      rcases first with ⟨left, right⟩ | ⟨right, left⟩
      all_goals rcases second with ⟨left_f, right_f⟩ | ⟨right_f, left_f⟩
      all_goals rw [← left, ← right, ← left_f, ← right_f]
      all_goals exact openSegment_symm ℝ _ _
    have nonempty : (G.edge e '' Set.Ioo (0 : unitInterval) 1).Nonempty := by
      rw [straight.open_edge_image e]
      exact ⟨midpoint ℝ _ _, midpoint_mem_openSegment _ _⟩
    obtain ⟨z, hz⟩ := nonempty
    exact Set.disjoint_left.mp (G.disjoint_open_edges e f different) hz (equal_images ▸ hz)

end Unfoldings.FiniteEmbeddedGraph
