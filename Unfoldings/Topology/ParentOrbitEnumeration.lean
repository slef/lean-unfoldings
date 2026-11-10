module

public import Unfoldings.Topology.ParentPaths
public import Unfoldings.Topology.SelectedSubtree

/-! Exact enumeration of the nonroot ancestors by the finite first-root orbit. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Finite V] (P : AscendingParents V)

/-- Each original nonroot ancestor occurs once before the parent orbit reaches its first root. -/
def nonrootAncestorEquiv (v : V) : Fin (P.distanceToRoot v) ≃
    {e : V // e ∉ P.roots ∧ P.Ancestor v e} :=
  Equiv.ofBijective (fun i => ⟨P.parent^[i.val] v,
    P.iterate_lt_distanceToRoot_not_mem v i.isLt, ⟨i.val, rfl⟩⟩) ⟨by
    intro i j same
    have vertices := congrArg Subtype.val same
    have heights := congrArg P.height vertices
    have indexes : i.castSucc = j.castSucc := (P.strictMono_height_rootOrbit v).injective heights
    exact Fin.castSucc_injective (P.distanceToRoot v) indexes, by
    rintro ⟨e, nonroot, n, reaches⟩
    have early : n < P.distanceToRoot v := by
      by_contra late
      have le := le_of_not_gt late
      have root_at_n : P.parent^[n] v ∈ P.roots := by
        rw [← Nat.sub_add_cancel le, Function.iterate_add_apply,
          Function.iterate_fixed (P.fixed_root _ (P.iterate_distanceToRoot_mem v))]
        exact P.iterate_distanceToRoot_mem v
      exact nonroot (reaches ▸ root_at_n)
    exact ⟨⟨n, early⟩, Subtype.ext reaches⟩⟩

variable [Fintype V]

open scoped Classical in
theorem sum_nonroot_ancestors (v : V) (weight : V → ℝ) :
    (∑ e : V, if e ∉ P.roots ∧ P.Ancestor v e then weight e else 0) =
      ∑ i : Fin (P.distanceToRoot v), weight (P.parent^[i.val] v) := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun e => e ∉ P.roots ∧ P.Ancestor v e)
    (Finset.univ.filter (fun e => e ∉ P.roots ∧ P.Ancestor v e))
    (by simp) weight).trans ((P.nonrootAncestorEquiv v).sum_comp (fun e => weight e.val)).symm

end Unfoldings.AscendingParents
