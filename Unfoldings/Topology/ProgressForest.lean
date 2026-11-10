module

public import Unfoldings.Topology.SelectedForest

/-!
# Construct forests from local progress

A local outgoing-edge existence lemma suffices: preserve a sector label and
increase its potential. Parent edges and the rooted forest are constructed,
not supplied. Geometric applications must prove the local progress lemma.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {V E Label : Type*} (G : Graph V E) (roots : Set V)
  (label : V → Label) (potential : Label → V → ℝ)

/-- Local admissible-edge existence; this does not assert a forest or acyclicity. -/
def HasLabeledProgress : Prop := ∀ v ∉ roots, ∃ w e,
  G.IsLink e v w ∧ label w = label v ∧ potential (label v) v < potential (label v) w

namespace HasLabeledProgress

variable {G roots label potential} (progress : HasLabeledProgress G roots label potential)

def nextVertex (v : {v : V // v ∉ roots}) : V := (progress v.val v.property).choose

def nextEdge (v : {v : V // v ∉ roots}) : E :=
  (progress v.val v.property).choose_spec.choose

theorem next_spec (v : {v : V // v ∉ roots}) :
    G.IsLink (progress.nextEdge v) v.val (progress.nextVertex v) ∧
      label (progress.nextVertex v) = label v.val ∧
        potential (label v.val) v.val < potential (label v.val) (progress.nextVertex v) :=
  (progress v.val v.property).choose_spec.choose_spec

open scoped Classical in
def parents : AscendingParents V where
  roots := roots
  parent v := if h : v ∈ roots then v else progress.nextVertex ⟨v, h⟩
  height v := potential (label v) v
  fixed_root v root := dite_eq_left root
  ascending v nonroot := by
    rw [dite_eq_right nonroot, (progress.next_spec ⟨v, nonroot⟩).2.1]
    exact (progress.next_spec ⟨v, nonroot⟩).2.2

def selection : progress.parents.EdgeSelection G where
  edge v := progress.nextEdge ⟨v.val, v.property⟩
  link v := by
    classical
    have nonroot : v.val ∉ roots := v.property
    change G.IsLink (progress.nextEdge ⟨v.val, nonroot⟩) v.val
      (if h : v.val ∈ roots then v.val else progress.nextVertex ⟨v.val, h⟩)
    rw [dite_eq_right nonroot]
    exact (progress.next_spec ⟨v.val, nonroot⟩).1

/-- The selected original graph edges form a rooted forest, with all vertices included. -/
theorem selected_rootedForest [Finite V] : progress.selection.graph.IsRootedForest roots :=
  progress.selection.graph_rootedForest

/-- Every selected edge in its outward orientation remains in its original sector label. -/
theorem parent_label (v : V) : label (progress.parents.parent v) = label v := by
  by_cases root : v ∈ roots
  · simp only [parents, dite_eq_left root]
  · simpa only [parents, dite_eq_right root] using (progress.next_spec ⟨v, root⟩).2.1

theorem ancestor_label {v w : V} (related : progress.parents.Ancestor v w) : label v = label w := by
  obtain ⟨n, rfl⟩ := related
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', progress.parent_label]
    exact ih

end HasLabeledProgress
end Unfoldings
