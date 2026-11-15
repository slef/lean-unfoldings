module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic

/-! Full-dimensional intersections suffice to refine an actual finite convex cover. -/

@[expose] public section

namespace Unfoldings

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]

/-- Discarding lower-dimensional intersections loses no point of a closed full convex region.
The finite covering pieces may be unbounded or redundant. -/
theorem full_convex_intersections_cover (s : Set E) (closed_s : IsClosed s)
    (convex_s : Convex ℝ s) (full_s : (interior s).Nonempty)
    (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
    (convex : ∀ i, Convex ℝ (cells i)) (full : ∀ i, (interior (cells i)).Nonempty)
    (cover : (⋃ i, cells i) = Set.univ) :
    s = ⋃ i : {i // (interior (s ∩ cells i)).Nonempty}, s ∩ cells i.val := by
  let selected := ⋃ i : {i // (interior (s ∩ cells i)).Nonempty}, s ∩ cells i.val
  have closed_selected : IsClosed selected :=
    isClosed_iUnion_of_finite (fun i => closed_s.inter (closed i.val))
  have interior_covered : interior s ⊆ selected := by
    intro x inside
    have covered : x ∈ ⋃ i, cells i := cover.symm ▸ Set.mem_univ x
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp covered
    have approached : x ∈ closure (interior (cells i)) := by
      rw [(convex i).closure_interior_eq_closure_of_nonempty_interior (full i),
        (closed i).closure_eq]
      exact member
    obtain ⟨r, rpos, near⟩ := Metric.isOpen_iff.mp isOpen_interior x inside
    obtain ⟨y, in_cell, close⟩ := Metric.mem_closure_iff.mp approached r rpos
    have intersection_full : (interior (s ∩ cells i)).Nonempty := by
      refine ⟨y, ?_⟩
      rw [interior_inter]
      exact ⟨near (Metric.mem_ball.mpr (by rwa [dist_comm])), in_cell⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, intersection_full⟩, interior_subset inside, member⟩
  apply Set.Subset.antisymm
  · have regular : closure (interior s) = s :=
      (convex_s.closure_interior_eq_closure_of_nonempty_interior full_s).trans closed_s.closure_eq
    exact regular.symm.le.trans
      (closure_minimal interior_covered closed_selected)
  · intro x member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact hi.1

end Unfoldings
