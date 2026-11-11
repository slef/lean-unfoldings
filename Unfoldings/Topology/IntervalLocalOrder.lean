module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith

/-! Local forward inequalities along an interval telescope to global endpoint inequalities. -/

@[expose] public section

namespace Unfoldings

/-- Any reflexive transitive relation that holds forward in local interval neighborhoods
holds between the endpoints. No continuity of the parametrized objects is needed. -/
theorem interval_relation_endpoints_of_local {X : Type*} (r : X → X → Prop)
    (reflexive : ∀ x, r x x)
    (transitive : ∀ {a b c}, r a b → r b c → r a c) (f : unitInterval → X)
    (local_order : ∀ t : unitInterval, ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
      ∀ a ∈ U, ∀ b ∈ U, a ≤ b → r (f a) (f b)) : r (f 0) (f 1) := by
  classical
  choose U opened member ordered using local_order
  obtain ⟨time, start, monotone, ⟨n, finish⟩, covered⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval opened
      (fun t _ => Set.mem_iUnion.mpr ⟨t, member t⟩)
  have progress (k : ℕ) : r (f (time 0)) (f (time k)) := by
    induction k with
    | zero => exact reflexive _
    | succ k ih =>
      obtain ⟨i, inside⟩ := covered k
      have ascending := monotone (Nat.le_succ k)
      exact transitive ih (ordered i (time k) (inside ⟨le_rfl, ascending⟩)
        (time (k + 1)) (inside ⟨ascending, le_rfl⟩) ascending)
  simpa only [start, finish n le_rfl] using progress n

/-- A uniform local lower bound for one developed coordinate survives the whole path. -/
theorem interval_coordinate_bound_of_local (input output : unitInterval → ℝ) (c : ℝ)
    (local_bound : ∀ t : unitInterval, ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
      ∀ a ∈ U, ∀ b ∈ U, a ≤ b →
        c * (input b - input a) ≤ output b - output a) :
    c * (input 1 - input 0) ≤ output 1 - output 0 := by
  apply interval_relation_endpoints_of_local
    (fun p q : ℝ × ℝ => c * (q.1 - p.1) ≤ q.2 - p.2)
    (fun _ => by simp only [sub_self, mul_zero, le_refl])
    (fun {_ _ _} first last => by nlinarith)
    (fun t => (input t, output t)) local_bound

end Unfoldings
