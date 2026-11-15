module

public import Unfoldings.Topology.ParentFrontierHistory

/-! First-contact processing explores exactly the original parent paths, without reprocessing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

variable {V : Type*} [Finite V] {P : AscendingParents V} (S : P.ParentFrontier)

omit [Finite V] in
/-- An already processed point has its entire original parent orbit in the frontier. -/
theorem iterate_mem_of_mem {v : V} (member : v ∈ S.processed) (k : ℕ) :
    P.parent^[k] v ∈ S.processed := by
  induction k with
  | zero => exact member
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact S.closed _ ih

/-- Original ancestor membership changes exactly once along the path: at first contact. -/
theorem contactTime_le_iff (v : V) (k : ℕ) :
    S.contactTime v ≤ k ↔ P.parent^[k] v ∈ S.processed := by
  classical
  constructor
  · intro later
    have closed := S.iterate_mem_of_mem (S.contact_mem v) (k - S.contactTime v)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel later] at closed
  · exact Nat.find_min' (S.exists_contact v)

theorem contactTime_eq_zero_iff (v : V) : S.contactTime v = 0 ↔ v ∈ S.processed := by
  simpa only [Nat.le_zero, Function.iterate_zero_apply] using S.contactTime_le_iff v 0

/-- A process step adds the whole original ancestor path; after contact that path was
already processed, so precisely the fresh prefix is newly added. -/
theorem mem_process_iff (v w : V) :
    w ∈ (S.process v).processed ↔ w ∈ S.processed ∨ P.Ancestor v w := by
  constructor
  · rintro (old | ⟨i, rfl⟩)
    · exact Or.inl old
    · exact Or.inr ⟨i.val, rfl⟩
  · rintro (old | ⟨k, rfl⟩)
    · exact Or.inl old
    · by_cases before : k < S.contactTime v
      · exact Or.inr ⟨⟨k, before⟩, rfl⟩
      · exact Or.inl ((S.contactTime_le_iff v k).mp (le_of_not_gt before))

/-- Processing a source again creates no fresh branch. -/
theorem contactTime_process_self (v : V) : (S.process v).contactTime v = 0 :=
  ((S.process v).contactTime_eq_zero_iff v).mpr ((S.mem_process_iff v v).mpr
    (Or.inr (P.ancestor_refl v)))

/-- The fresh branch is exactly the original unprocessed nonroot ancestor set. -/
theorem mem_freshBranch_iff (v : V) (w : {w : V // w ∉ P.roots}) :
    w ∈ S.freshBranch v ↔ w.val ∉ S.processed ∧ P.Ancestor v w.val := by
  constructor
  · intro member
    refine ⟨S.freshBranch_avoids_processed v w member, ?_⟩
    obtain ⟨i, equal⟩ := List.mem_ofFn.mp member
    exact ⟨i.val, congrArg Subtype.val equal⟩
  · rintro ⟨outside, k, equal⟩
    have before : k < S.contactTime v := by
      by_contra later
      exact outside (equal ▸ (S.contactTime_le_iff v k).mp (le_of_not_gt later))
    exact List.mem_ofFn.mpr ⟨⟨k, before⟩, Subtype.ext equal⟩

/-- The accumulated charge list consists exactly of unprocessed original vertices reached
from the given seeds, independently of their order or repetition. -/
theorem mem_history_iff (seeds : List V) (w : {w : V // w ∉ P.roots}) :
    w ∈ S.history seeds ↔
      w.val ∉ S.processed ∧ ∃ v ∈ seeds, P.Ancestor v w.val := by
  induction seeds generalizing S with
  | nil => simp [history]
  | cons v seeds ih =>
    rw [history, List.mem_append, S.mem_freshBranch_iff, ih]
    constructor
    · rintro (⟨outside, current⟩ | ⟨outside, u, member, ancestor⟩)
      · exact ⟨outside, v, List.mem_cons_self, current⟩
      · exact ⟨fun old => outside (Or.inl old), u, List.mem_cons_of_mem v member, ancestor⟩
    · rintro ⟨outside, u, member, ancestor⟩
      by_cases current : P.Ancestor v w.val
      · exact Or.inl ⟨outside, current⟩
      · have old_seed : u ∈ seeds := by
          rcases List.mem_cons.mp member with same | member
          · exact (current (same ▸ ancestor)).elim
          · exact member
        refine Or.inr ⟨?_, u, old_seed, ancestor⟩
        intro processed
        exact ((S.mem_process_iff v w.val).mp processed).elim outside current

/-- Keep the actual updated processed state after the entire seed list. -/
def run (S : P.ParentFrontier) (seeds : List V) : P.ParentFrontier :=
  seeds.foldl (fun frontier v => frontier.process v) S

/-- The resulting processed frontier is precisely the old frontier and the seeds' actual
original parent paths. No path-cover certificate is assumed for intermediate states. -/
theorem mem_run_iff (seeds : List V) (w : V) :
    w ∈ (S.run seeds).processed ↔ w ∈ S.processed ∨ ∃ v ∈ seeds, P.Ancestor v w := by
  induction seeds generalizing S with
  | nil => simp [run]
  | cons v seeds ih =>
    change w ∈ ((S.process v).run seeds).processed ↔ _
    rw [ih, S.mem_process_iff]
    constructor
    · rintro ((old | current) | ⟨u, member, ancestor⟩)
      · exact Or.inl old
      · exact Or.inr ⟨v, List.mem_cons_self, current⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem v member, ancestor⟩
    · rintro (old | ⟨u, member, ancestor⟩)
      · exact Or.inl (Or.inl old)
      · rcases List.mem_cons.mp member with same | member
        · exact Or.inl (Or.inr (same ▸ ancestor))
        · exact Or.inr ⟨u, member, ancestor⟩

end Unfoldings.AscendingParents.ParentFrontier
