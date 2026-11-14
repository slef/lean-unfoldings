module

public import Unfoldings.Convex.ExteriorPlan
public import Unfoldings.Topology.ParentPaths

/-! First root contacts produce a finite forest followed by straight terminal rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} [Finite V] (R : E.ExteriorPlan V)

theorem exists_first_contact (v : V) (has : ∃ w, R.Contact v w) :
    ∃ w, R.Contact v w ∧ ∀ z, R.Contact v z → E.height (R.point w) ≤ E.height (R.point z) := by
  classical
  let := Fintype.ofFinite V
  let candidates := Finset.univ.filter (R.Contact v)
  have nonempty : candidates.Nonempty := by
    obtain ⟨w, hw⟩ := has
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
  obtain ⟨w, hw, least⟩ := candidates.exists_min_image (fun w => E.height (R.point w)) nonempty
  exact ⟨w, (Finset.mem_filter.mp hw).2,
    fun z hz => least z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)⟩

/-- A terminal root has no other prescribed root on its positive ray. -/
def terminal : Set V := {v | ¬ ∃ w, R.Contact v w}

open Classical in
def next (v : V) : V :=
  if has : ∃ w, R.Contact v w then (R.exists_first_contact v has).choose else v

theorem next_spec {v : V} (nonterminal : v ∉ R.terminal) :
    R.Contact v (R.next v) ∧
      ∀ z, R.Contact v z → E.height (R.point (R.next v)) ≤ E.height (R.point z) := by
  classical
  have has : ∃ w, R.Contact v w := not_not.mp nonterminal
  rw [next, dite_eq_left has]
  exact (R.exists_first_contact v has).choose_spec

open Classical in
/-- Parent choices are the first actual contacts. Positive ray rates prove strict ascent. -/
def parents : AscendingParents V where
  roots := R.terminal
  parent := R.next
  height v := E.height (R.point v)
  fixed_root v terminal := by
    rw [next, dite_eq_right terminal]
  ascending _ nonterminal := R.contact_height_lt (R.next_spec nonterminal).1

theorem rootedForest : R.parents.graph.IsRootedForest R.terminal :=
  R.parents.graph_rootedForest

/-- The unique final root has a straight continuation with no further contacts. -/
theorem final_ray_no_contacts (v w : V) {t : ℝ} (positive : 0 < t) :
    R.ray (R.parents.root v) t ≠ R.point w := by
  intro equal
  have terminal := R.parents.root_mem v
  exact terminal ⟨w, t, positive, equal.symm⟩

/-- The retained open part of a ray ends before its first prescribed root, or extends
forever when there is no root contact. This definition includes the terminal tails. -/
def openPiece (v : V) : Set Plane :=
  {x | ∃ t : ℝ, 0 < t ∧ x = R.ray v t ∧
    ∀ w, R.Contact v w → E.height x < E.height (R.point w)}

omit [Finite V] in
theorem openPiece_subset_openRay (v : V) : R.openPiece v ⊆ R.openRay v :=
  fun _ ⟨t, ht, equal, _⟩ => ⟨t, ht, equal⟩

omit [Finite V] in
theorem openPiece_avoids_roots (v w : V) : R.point w ∉ R.openPiece v := by
  rintro ⟨t, positive, equal, before⟩
  exact lt_irrefl _ (before w ⟨t, positive, equal⟩)

omit [Finite V] in
theorem terminal_openPiece_eq {v : V} (terminal : v ∈ R.terminal) :
    R.openPiece v = R.openRay v := by
  apply Set.Subset.antisymm (R.openPiece_subset_openRay v)
  rintro x ⟨t, ht, equal⟩
  exact ⟨t, ht, equal, fun w contact => False.elim (terminal ⟨w, contact⟩)⟩

/-- Every point strictly before the first contact belongs to the retained open piece. -/
theorem before_first_contact {v : V} (nonterminal : v ∉ R.terminal) {T t : ℝ}
    (contact_time : R.point (R.next v) = R.ray v T) (Tpos : 0 < T)
    (tpos : 0 < t) (before : t < T) : R.ray v t ∈ R.openPiece v := by
  refine ⟨t, tpos, rfl, ?_⟩
  intro w contact
  have least := (R.next_spec nonterminal).2 w contact
  rw [contact_time, R.height_ray v Tpos.le] at least
  rw [R.height_ray v tpos.le]
  have ratepos : 0 < R.rate v := R.positive v
  nlinarith

end Unfoldings.SlopeEnvelope.ExteriorPlan
