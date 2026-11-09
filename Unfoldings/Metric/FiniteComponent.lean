module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Finite-distance components of an extended metric space

Disconnected cut surfaces can have infinite distances. Each finite-distance
component is nevertheless a clopen ordinary metric subspace, compact whenever
the extended metric space is compact. The metric construction preserves its
original extended distance and topology definitionally.
-/

@[expose] public section

open scoped ENNReal Topology

namespace Unfoldings

variable {X : Type*} [EMetricSpace X]

theorem finite_edist_trans {x y z : X} (left : edist x y ≠ ⊤) (right : edist y z ≠ ⊤) :
    edist x z ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨left, right⟩) (edist_triangle x y z)

/-- All points at finite extended distance from a fixed point. -/
def finiteComponent (p : X) : Set X := {x | edist x p ≠ ⊤}

theorem isOpen_finiteComponent (p : X) : IsOpen (finiteComponent p) :=
  isOpen_ne.preimage (continuous_id.edist continuous_const)

theorem isClosed_finiteComponent (p : X) : IsClosed (finiteComponent p) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have near : finiteComponent x ∈ 𝓝 x :=
    (isOpen_finiteComponent x).mem_nhds (by simp [finiteComponent])
  apply Filter.mem_of_superset near
  intro y hy inside
  exact hx (finite_edist_trans (by simpa only [finiteComponent, Set.mem_ofPred_eq,
    edist_comm] using hy) inside)

/-- The component as an ordinary metric space with its original subspace topology. -/
abbrev FiniteComponent (p : X) : Type _ := finiteComponent p

namespace FiniteComponent

noncomputable instance (p : X) : MetricSpace (FiniteComponent p) :=
  EMetricSpace.toMetricSpace (fun x y => by
    change edist x.val y.val ≠ ⊤
    exact finite_edist_trans (x := x.val) (y := p) (z := y.val) x.property
      (by simpa only [finiteComponent, Set.mem_ofPred_eq, edist_comm] using y.property))

instance [CompactSpace X] (p : X) : CompactSpace (FiniteComponent p) :=
  isCompact_iff_compactSpace.mp (isClosed_finiteComponent p).isCompact

/-- The original point belongs to its own finite-distance component. -/
def center (p : X) : FiniteComponent p := ⟨p, by simp [finiteComponent]⟩

theorem val_isometry (p : X) : Isometry (Subtype.val : FiniteComponent p → X) :=
  fun _ _ => rfl

@[simp] theorem edist_eq (p : X) (x y : FiniteComponent p) :
    edist x y = edist x.val y.val := rfl

end FiniteComponent
end Unfoldings
