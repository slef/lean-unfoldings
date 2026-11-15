module

public import Unfoldings.Topology.ParentPaths
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup

/-! Construct fresh parent branches up to their first contact with an already processed frontier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} (P : AscendingParents V)

/-- The processed ancestor set includes the boundary roots and every parent of a processed vertex.
It records combinatorial contact, without assuming geometric saved-frontier placement. -/
structure ParentFrontier where
  processed : Set V
  roots : P.roots ⊆ processed
  closed : ∀ v ∈ processed, P.parent v ∈ processed

/-- Before processing any branch, only the original boundary roots are marked. -/
def initialFrontier : P.ParentFrontier where
  processed := P.roots
  roots := Set.Subset.refl _
  closed := by intro v root; rwa [P.fixed_root v root]

namespace ParentFrontier

variable {P} [Finite V] (S : P.ParentFrontier)

theorem exists_contact (v : V) : ∃ n : ℕ, P.parent^[n] v ∈ S.processed :=
  ⟨P.distanceToRoot v, S.roots (P.iterate_distanceToRoot_mem v)⟩

open Classical in
/-- The first already processed ancestor, with zero length when the source is processed. -/
def contactTime (v : V) : ℕ := Nat.find (S.exists_contact v)

theorem contact_mem (v : V) : P.parent^[S.contactTime v] v ∈ S.processed := by
  classical
  exact Nat.find_spec (S.exists_contact v)

theorem before_contact_not_mem (v : V) {k : ℕ} (before : k < S.contactTime v) :
    P.parent^[k] v ∉ S.processed := by
  classical
  exact Nat.find_min (S.exists_contact v) before

theorem before_contact_nonroot (v : V) {k : ℕ} (before : k < S.contactTime v) :
    P.parent^[k] v ∉ P.roots := fun root => S.before_contact_not_mem v before (S.roots root)

theorem contactTime_le_root (v : V) : S.contactTime v ≤ P.distanceToRoot v := by
  classical
  exact Nat.find_min' (S.exists_contact v) (S.roots (P.iterate_distanceToRoot_mem v))

/-- Original named nonroots on the fresh branch, excluding the first processed contact. -/
def freshBranch (v : V) : List {w : V // w ∉ P.roots} :=
  List.ofFn (fun i : Fin (S.contactTime v) =>
    ⟨P.parent^[i.val] v, S.before_contact_nonroot v i.isLt⟩)

/-- The next state adjoins precisely the fresh branch, keeping the old frontier. -/
def process (v : V) : P.ParentFrontier where
  processed := S.processed ∪ Set.range (fun i : Fin (S.contactTime v) => P.parent^[i.val] v)
  roots := fun _ member => Or.inl (S.roots member)
  closed := by
    intro w member
    rcases member with old | ⟨i, rfl⟩
    · exact Or.inl (S.closed _ old)
    · by_cases before : i.val + 1 < S.contactTime v
      · exact Or.inr ⟨⟨i.val + 1, before⟩, Function.iterate_succ_apply' _ _ _⟩
      · have last : i.val + 1 = S.contactTime v := by omega
        apply Or.inl
        rw [← Function.iterate_succ_apply' P.parent i.val v]
        change P.parent^[i.val + 1] v ∈ S.processed
        rw [last]
        exact S.contact_mem v

/-- No original vertex repeats along the fresh branch, including its contact endpoint. -/
theorem strictMono_height_contact (v : V) :
    StrictMono (fun i : Fin (S.contactTime v + 1) => P.height (P.parent^[i.val] v)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change P.height (P.parent^[i.val] v) < P.height (P.parent^[i.val + 1] v)
  rw [Function.iterate_succ_apply']
  exact P.ascending _ (S.before_contact_nonroot v i.isLt)

theorem freshBranch_nodup (v : V) : (S.freshBranch v).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j equal
  have vertices := congrArg Subtype.val equal
  have indices : i.castSucc = j.castSucc := (S.strictMono_height_contact v).injective
    (show P.height (P.parent^[i.val] v) = P.height (P.parent^[j.val] v) from
      congrArg P.height vertices)
  apply Fin.ext
  exact congrArg (fun k : Fin (S.contactTime v + 1) => k.val) indices

theorem freshBranch_avoids_processed (v : V) (w : {w : V // w ∉ P.roots})
    (member : w ∈ S.freshBranch v) : w.val ∉ S.processed := by
  obtain ⟨i, equal⟩ := List.mem_ofFn.mp member
  have actual := congrArg Subtype.val equal
  exact actual ▸ S.before_contact_not_mem v i.isLt

theorem freshBranch_mem_process (v : V) (w : {w : V // w ∉ P.roots})
    (member : w ∈ S.freshBranch v) : w.val ∈ (S.process v).processed := by
  obtain ⟨i, equal⟩ := List.mem_ofFn.mp member
  exact Or.inr ⟨i, congrArg Subtype.val equal⟩

/-- Process any original seed list by first contact; each step uses the updated frontier. -/
def history (S : P.ParentFrontier) : List V → List {w : V // w ∉ P.roots}
  | [] => []
  | v :: rest => S.freshBranch v ++ (S.process v).history rest

/-- The entire actual first-contact history avoids the already processed original vertices. -/
theorem history_avoids_processed (seeds : List V) (w : {w : V // w ∉ P.roots})
    (member : w ∈ S.history seeds) : w.val ∉ S.processed := by
  induction seeds generalizing S with
  | nil => simp only [history, List.not_mem_nil] at member
  | cons v seeds ih =>
    rcases List.mem_append.mp member with fresh | later
    · exact S.freshBranch_avoids_processed v w fresh
    · exact fun old => ih (S.process v) later (Or.inl old)

/-- Fresh original curvature vertices are charged only once, for every processing order.
Distinctness is derived from the constructed first-contact history. -/
theorem history_nodup (seeds : List V) : (S.history seeds).Nodup := by
  induction seeds generalizing S with
  | nil => exact List.nodup_nil
  | cons v seeds ih =>
    apply List.nodup_append'.mpr
    refine ⟨S.freshBranch_nodup v, ih (S.process v), ?_⟩
    apply List.disjoint_left.mpr
    intro w fresh later
    exact (S.process v).history_avoids_processed seeds w later (S.freshBranch_mem_process v w fresh)

end ParentFrontier

end Unfoldings.AscendingParents
