module

public import Unfoldings.Roof.GraphLensFaceAngles
public import Unfoldings.Topology.GraphLensInterior

/-! The exact signed curvature identity for the closing-graph lens comparison. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

open Real

/-- In the forward traversal the negative lens sign is positive precisely
on the side above the closing graph. -/
theorem graphLens_negSign_mul_height_pos {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (ordered : a < b) (first : f a = g a) (last : f b = g b)
    (separate : ∀ t ∈ Set.Ioo a b, f t ≠ g t) {p : Plane}
    (inside : p ∈ interior (closedJordanDomain (graphLens f g a b))) :
    0 < (p 1 - g (p 0)) * (-graphLensSign f g a b) := by
  rw [interior_closedJordanDomain_graphLens hf hg ordered first last separate] at inside
  have mid : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith only [ordered], by linarith only [ordered]⟩
  have interval : p 0 ∈ Set.Ioo a b := inside.1
  have order := graph_order_iff_at hf hg mid interval separate
  by_cases below : f ((a + b) / 2) < g ((a + b) / 2)
  · have local_order := order.mp below
    have h : p 1 < g (p 0) := (inside.2.2).trans_eq (max_eq_right local_order.le)
    rw [graphLensSign, ite_eq_left below]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr h) (by norm_num)
  · have local_order : g (p 0) < f (p 0) :=
      lt_of_le_of_ne (le_of_not_gt (fun h => below (order.mpr h))) (separate _ interval).symm
    have h : g (p 0) < p 1 := (min_eq_right local_order.le).symm.trans_lt inside.2.1
    rw [graphLensSign, ite_eq_right below]
    exact mul_pos (sub_pos.mpr h) (by norm_num)

end Unfoldings.PlanarTopology
