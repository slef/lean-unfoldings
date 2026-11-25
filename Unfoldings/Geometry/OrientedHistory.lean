module

public import Unfoldings.Geometry.OrientedSubsegments
public import Unfoldings.Geometry.PolygonalChain
public import Mathlib.Tactic.Module

/-! Directed mesh subedges preserve headings and component labels along a chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteEmbeddedGraph

variable {V E X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {G : FiniteEmbeddedGraph V E X}

theorem OrientedSubsegment.displacement {x y : X} (S : G.OrientedSubsegment x y) :
    y - x = (S.last - S.first) • (G.vertex (G.right S.edge) - G.vertex (G.left S.edge)) := by
  calc
    y - x = _ := congrArg₂ (· - ·) S.at_last.symm S.at_first.symm
    _ = _ := by simp only [AffineMap.lineMap_apply_module']; module

variable {Label : Type*} (label : V → Label)
  (constant : ∀ e, label (G.left e) = label (G.right e))

include constant in
private theorem labels_equal_of_reachable {x y : V} (reachable : G.adjacencyGraph.Reachable x y) :
    label x = label y := by
  obtain ⟨walk⟩ := reachable
  induction walk with
  | nil => rfl
  | cons link _ ih =>
    apply Eq.trans _ ih
    obtain ⟨e, first | last⟩ := link.2
    · rw [first.1, first.2]
      exact constant e
    · rw [last.1, last.2]
      exact (constant e).symm

include constant in
/-- Coarse edges meeting at any point of their closed segments carry the
same component label. This includes meetings at a shared endpoint. -/
theorem labels_equal_of_closed_edge_contact (straight : G.IsStraight) {e f : E} {x : X}
    (first : x ∈ segment ℝ (G.vertex (G.left e)) (G.vertex (G.right e)))
    (last : x ∈ segment ℝ (G.vertex (G.left f)) (G.vertex (G.right f))) :
    label (G.left e) = label (G.left f) := by
  obtain ⟨s, s_in, at_first⟩ := (segment_eq_image_lineMap ℝ _ _).subset first
  obtain ⟨t, t_in, at_last⟩ := (segment_eq_image_lineMap ℝ _ _).subset last
  let u : unitInterval := ⟨s, s_in⟩
  let v : unitInterval := ⟨t, t_in⟩
  have located_first : G.edge e u = x := (straight e u).trans at_first
  have located_last : G.edge f v = x := (straight f v).trans at_last
  exact labels_equal_of_reachable label constant
    (G.edges_intersection_reachable e f u v (located_first.trans located_last.symm))

include constant in
/-- The whole directed fine history stays in the same labeled coarse
component. The outgoing edge at a merger keeps the label of both stems. -/
theorem chain_labels_const (straight : G.IsStraight) {n : ℕ} (positive : 0 < n)
    (P : PolygonalChain X n)
    (step : ∀ i, G.OrientedSubsegment (P.vertex i.castSucc) (P.vertex i.succ))
    (i : Fin n) :
    label (G.left (step i).edge) = label (G.left (step ⟨0, positive⟩).edge) := by
  have adjacent {i j : Fin n} (next : j.val = i.val + 1) :
      label (G.left (step j).edge) = label (G.left (step i).edge) := by
    have first := (step j).first_mem_halfOpen straight
    have last := lineMap_mem_segment ℝ (G.vertex (G.left (step i).edge))
      (G.vertex (G.right (step i).edge)) (step i).last_mem
    have equal : P.vertex i.succ = P.vertex j.castSucc :=
      congrArg P.vertex (Fin.ext next.symm)
    have in_last : P.vertex j.castSucc ∈
        segment ℝ (G.vertex (G.left (step i).edge)) (G.vertex (G.right (step i).edge)) :=
      (congrArg (fun x => x ∈ segment ℝ (G.vertex (G.left (step i).edge))
        (G.vertex (G.right (step i).edge))) ((step i).at_last.trans equal)).mp last
    exact labels_equal_of_closed_edge_contact label constant straight first.1 in_last
  have chain : ∀ k (bounds : k < n),
      label (G.left (step ⟨k, bounds⟩).edge) =
        label (G.left (step ⟨0, positive⟩).edge) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro bounds
      have pred : k < n := by omega
      exact (adjacent (i := ⟨k, pred⟩) (j := ⟨k + 1, bounds⟩) rfl).trans (ih pred)
  exact chain i.val i.isLt

end Unfoldings.FiniteEmbeddedGraph
