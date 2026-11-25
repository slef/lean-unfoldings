module

public import Unfoldings.Topology.TwoGraphJordan
public import Mathlib.Topology.Order.IntermediateValue

/-! The side of a graph is constant on a connected cell that avoids the graph and the end lines. -/

@[expose] public section

namespace Unfoldings.PlanarTopology

/-- Two points of a connected cell give the same test for being above the
graph in its horizontal interval. This lets local bank germs select whole
triangles by any one of their interior samples. -/
theorem aboveGraph_iff_of_cell {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    {cell : Set Plane} (connected : IsPreconnected cell)
    (endpoints : ∀ z ∈ cell, z 0 ≠ a ∧ z 0 ≠ b)
    (avoids : Disjoint cell (graphPoint f '' Set.Icc a b))
    {p q : Plane} (p_in : p ∈ cell) (q_in : q ∈ cell) :
    (p 0 ∈ Set.Ioo a b ∧ f (p 0) < p 1) ↔ (q 0 ∈ Set.Ioo a b ∧ f (q 0) < q 1) := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  let y := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1
  have horizontal : IsPreconnected (x '' cell) := connected.image _ x.continuous.continuousOn
  have time {z : Plane} (hz : z ∈ cell) (inside : z 0 ∈ Set.Ioo a b)
      (w : Plane) (hw : w ∈ cell) : w 0 ∈ Set.Ioo a b := by
    have after : a < w 0 := by
      by_contra! before
      obtain ⟨v, hv, same⟩ := horizontal.Icc_subset (Set.mem_image_of_mem x hw)
        (Set.mem_image_of_mem x hz) (show a ∈ Set.Icc (x w) (x z) from ⟨before, inside.1.le⟩)
      exact (endpoints v hv).1 same
    have before : w 0 < b := by
      by_contra! after
      obtain ⟨v, hv, same⟩ := horizontal.Icc_subset (Set.mem_image_of_mem x hz)
        (Set.mem_image_of_mem x hw) (show b ∈ Set.Icc (x z) (x w) from ⟨inside.2.le, after⟩)
      exact (endpoints v hv).2 same
    exact ⟨after, before⟩
  let height (z : Plane) := y z - f (x z)
  have height_continuous : Continuous height := y.continuous.sub (hf.comp x.continuous)
  have vertical : IsPreconnected (height '' cell) := connected.image _ height_continuous.continuousOn
  have forward {z w : Plane} (hz : z ∈ cell) (hw : w ∈ cell)
      (above : z 0 ∈ Set.Ioo a b ∧ f (z 0) < z 1) : w 0 ∈ Set.Ioo a b ∧ f (w 0) < w 1 := by
    refine ⟨time hz above.1 w hw, ?_⟩
    by_contra! below
    obtain ⟨v, v_in, equal⟩ := vertical.Icc_subset (Set.mem_image_of_mem height hw)
      (Set.mem_image_of_mem height hz) (show (0 : ℝ) ∈ Set.Icc (height w) (height z) from
        ⟨sub_nonpos.mpr below, sub_nonneg.mpr above.2.le⟩)
    have at_graph : v ∈ graphPoint f '' Set.Icc a b := by
      refine ⟨v 0, Set.Ioo_subset_Icc_self (time hz above.1 v v_in), ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact (sub_eq_zero.mp equal).symm
    exact Set.disjoint_left.mp avoids v_in at_graph
  exact ⟨forward p_in q_in, forward q_in p_in⟩

end Unfoldings.PlanarTopology
