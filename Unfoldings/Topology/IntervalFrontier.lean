module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-! A bounded open angular window with at most two frontier points is one interval. -/

@[expose] public section

namespace Unfoldings

theorem isOpen_eq_Ioo_of_subset_frontier {U : Set ℝ} {a b : ℝ} (opened : IsOpen U)
    (inside : U ⊆ Set.Ioo a b) (boundary : frontier U ⊆ {a, b}) (nonempty : U.Nonempty) :
    U = Set.Ioo a b := by
  have disjoint : Disjoint U (closure U)ᶜ := Set.disjoint_left.mpr
    (fun _ member outside => outside (subset_closure member))
  have cover : Set.Ioo a b ⊆ U ∪ (closure U)ᶜ := by
    intro x between
    by_cases member : x ∈ U
    · exact Or.inl member
    · right
      intro limit
      have frontier : x ∈ frontier U := ⟨limit, fun interior => member (interior_subset interior)⟩
      rcases boundary frontier with first | last
      · exact (ne_of_gt between.1) first
      · exact (ne_of_lt between.2) (Set.mem_singleton_iff.mp last)
  rcases IsPreconnected.subset_or_subset opened isClosed_closure.isOpen_compl disjoint cover
      isPreconnected_Ioo with included | outside
  · exact Set.Subset.antisymm inside included
  · obtain ⟨x, member⟩ := nonempty
    exact (outside (inside member) (subset_closure member)).elim

/-- Boundedness excludes the two unbounded complementary intervals. If the only
possible frontier points are the ordered pair, a nonempty open set fills their gap. -/
theorem isOpen_bounded_eq_Ioo_of_frontier_subset {U : Set ℝ} {a b : ℝ} (opened : IsOpen U)
    (below : BddBelow U) (above : BddAbove U) (nonempty : U.Nonempty) (ordered : a ≤ b)
    (boundary : frontier U ⊆ {a, b}) : a < b ∧ U = Set.Ioo a b := by
  have inf_outside : sInf U ∉ U := by
    intro member
    obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp opened _ member
    have near : sInf U - ε / 2 ∈ U := ball (by
      rw [Metric.mem_ball, Real.dist_eq, show sInf U - ε / 2 - sInf U = -(ε / 2) by ring,
        abs_neg, abs_of_pos (half_pos positive)]
      linarith)
    have lower := csInf_le below near
    linarith
  have sup_outside : sSup U ∉ U := by
    intro member
    obtain ⟨ε, positive, ball⟩ := Metric.isOpen_iff.mp opened _ member
    have near : sSup U + ε / 2 ∈ U := ball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos positive)]
      linarith)
    have upper := le_csSup above near
    linarith
  have inf_boundary : sInf U ∈ frontier U :=
    ⟨csInf_mem_closure nonempty below, fun member => inf_outside (interior_subset member)⟩
  have sup_boundary : sSup U ∈ frontier U :=
    ⟨csSup_mem_closure nonempty above, fun member => sup_outside (interior_subset member)⟩
  have strict_member {x : ℝ} (member : x ∈ U) : sInf U < x ∧ x < sSup U :=
    ⟨lt_of_le_of_ne (csInf_le below member) (fun same => inf_outside (same ▸ member)),
      lt_of_le_of_ne (le_csSup above member) (fun same => sup_outside (same ▸ member))⟩
  obtain ⟨x, member⟩ := nonempty
  have gap : sInf U < sSup U := (strict_member member).1.trans (strict_member member).2
  have extremes : sInf U = a ∧ sSup U = b := by
    have first := boundary inf_boundary
    have last := boundary sup_boundary
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at first last
    rcases first with first | first <;> rcases last with last | last <;> constructor <;> linarith
  have between : U ⊆ Set.Ioo a b := by
    intro x member
    change a < x ∧ x < b
    simpa only [extremes.1, extremes.2] using strict_member member
  exact ⟨by linarith [extremes.1, extremes.2],
    isOpen_eq_Ioo_of_subset_frontier opened between boundary ⟨x, member⟩⟩

end Unfoldings
