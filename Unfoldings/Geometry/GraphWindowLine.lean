module

public import Unfoldings.Geometry.GraphWindowSide
public import Unfoldings.Geometry.Affine

/-! A forward graph segment gives the same signed side test as its supporting line. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- In the horizontal interval of a forward graph segment, signed area is
horizontal advance times the signed height above the graph. -/
theorem orient_eq_graph_height_of_segment {f : ℝ → ℝ} {a b : ℝ} {r s z : Plane}
    (forward : r 0 < s 0) (trace : segment ℝ r s ⊆ graphPoint f '' Set.Icc a b)
    (window : z 0 ∈ Set.Icc (r 0) (s 0)) :
    orient r s z = (s 0 - r 0) * (z 1 - f (z 0)) := by
  let w := s 0 - r 0
  let t := (z 0 - r 0) / w
  have positive : 0 < w := sub_pos.mpr forward
  have param : t ∈ Set.Icc 0 1 := ⟨div_nonneg (sub_nonneg.mpr window.1) positive.le,
    (div_le_one₀ positive).mpr (sub_le_sub_right window.2 _)⟩
  let q := AffineMap.lineMap r s t
  have member : q ∈ segment ℝ r s := lineMap_mem_segment _ _ _ param
  have horizontal : q 0 = z 0 := by
    dsimp only [q]
    rw [AffineMap.lineMap_apply_module']
    change t * w + r 0 = z 0
    dsimp only [t]
    rw [div_mul_cancel₀ _ positive.ne', sub_add_cancel]
  have vertical : q 1 = f (z 0) := by
    obtain ⟨u, _, at_u⟩ := trace member
    have time : u = z 0 := (congrArg (fun p : Plane => p 0) at_u).trans horizontal
    exact (congrArg (fun p : Plane => p 1) at_u).symm.trans (congrArg f time)
  have flat := orient_eq_zero_of_mem_segment member
  simp only [orient, horizontal, vertical] at flat ⊢
  linear_combination flat

/-- Any aligned original face meeting the middle of a straight forward graph
segment can be classified by its side of that line. -/
theorem interiorAboveGraph_iff_orient_of_midpoint {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} {r s : Plane} {S : Set Plane}
    (convex : Convex ℝ S) (nonempty : (interior S).Nonempty)
    (aligned : Disjoint (interior S) (graphPoint f '' Set.Icc a b))
    (forward : r 0 < s 0) (trace : segment ℝ r s ⊆ graphPoint f '' Set.Icc a b)
    (member : midpoint ℝ r s ∈ S) :
    ∃ z ∈ interior S, interiorAboveGraph f a b S ↔ 0 < orient r s z := by
  have times (z : Plane) (on_trace : z ∈ graphPoint f '' Set.Icc a b) : z 0 ∈ Set.Icc a b := by
    obtain ⟨t, interval, rfl⟩ := on_trace
    exact interval
  have starts := times r (trace (left_mem_segment ℝ r s))
  have finishes := times s (trace (right_mem_segment ℝ r s))
  have center : (midpoint ℝ r s) 0 ∈ Set.Ioo (r 0) (s 0) := by
    rw [midpoint, AffineMap.lineMap_apply_module']
    change r 0 < (2 : ℝ)⁻¹ * (s 0 - r 0) + r 0 ∧ (2 : ℝ)⁻¹ * (s 0 - r 0) + r 0 < s 0
    constructor <;> linarith only [forward]
  obtain ⟨z, hz, within⟩ := exists_interior_mem_window_of_mem_face convex nonempty member center
  have global : z 0 ∈ Set.Ioo a b := ⟨starts.1.trans_lt within.1, within.2.trans_le finishes.2⟩
  refine ⟨z, hz, (interiorAboveGraph_iff_of_mem_window hf convex aligned hz global).trans ?_⟩
  rw [orient_eq_graph_height_of_segment forward trace (Set.Ioo_subset_Icc_self within)]
  constructor
  · intro above
    exact mul_pos (sub_pos.mpr forward) (sub_pos.mpr above)
  · intro positive
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (sub_pos.mpr forward)).mp positive)

end Unfoldings.PlanarTopology
