module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Order.IntermediateValue

/-! Finitely many exceptions do not obstruct a continuous closed interval's closed coverage. -/

@[expose] public section

namespace Unfoldings

/-- A continuous curve on a genuine closed interval belongs everywhere to a closed set
if only finitely many parameters can fail. This also retains both endpoints. -/
theorem continuous_Icc_mem_closed_of_finite_exceptions {X : Type*} [TopologicalSpace X]
    {T : ℝ} (positive : 0 < T) (f : Set.Icc (0 : ℝ) T → X) (continuous : Continuous f)
    {S : Set X} (closed : IsClosed S) (exceptions : {t | f t ∉ S}.Finite) : ∀ t, f t ∈ S := by
  let : ConnectedSpace (Set.Icc (0 : ℝ) T) := isConnected_iff_connectedSpace.mp
    (isConnected_Icc positive.le)
  let : Nontrivial (Set.Icc (0 : ℝ) T) :=
    ⟨⟨⟨0, le_rfl, positive.le⟩, ⟨T, positive.le, le_rfl⟩,
      fun equal => positive.ne (congrArg Subtype.val equal)⟩⟩
  let : PerfectSpace (Set.Icc (0 : ℝ) T) := inferInstance
  intro t
  by_contra outside
  have open_bad : IsOpen {t | f t ∉ S} := closed.isOpen_compl.preimage continuous
  exact infinite_of_mem_nhds t (open_bad.mem_nhds outside) exceptions

end Unfoldings
