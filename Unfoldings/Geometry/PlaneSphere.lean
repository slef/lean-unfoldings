module

public import Unfoldings.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Perfect

/-! The planar unit circle is connected, nontrivial, and has no isolated points. -/

@[expose] public section

namespace Unfoldings

theorem plane_unit_sphere_connected : ConnectedSpace (Metric.sphere (0 : Plane) 1) := by
  have dimension : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  exact isConnected_iff_connectedSpace.mp (isConnected_sphere dimension 0 zero_le_one)

theorem plane_unit_sphere_nontrivial : Nontrivial (Metric.sphere (0 : Plane) 1) := by
  obtain ⟨u, norm_u⟩ := exists_norm_eq Plane (zero_le_one : (0 : ℝ) ≤ 1)
  have member : u ∈ Metric.sphere (0 : Plane) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_u
  have negative : -u ∈ Metric.sphere (0 : Plane) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using norm_u
  refine ⟨⟨⟨u, member⟩, ⟨-u, negative⟩, ?_⟩⟩
  intro equal
  have vectors := congrArg Subtype.val equal
  have doubled : (2 : ℝ) • u = 0 := by
    have sum := congrArg (fun x : Plane => x + u) vectors
    simpa only [neg_add_cancel, two_smul] using sum
  have zero : u = 0 := (smul_eq_zero.mp doubled).resolve_left (by norm_num)
  rw [zero, norm_zero] at norm_u
  exact zero_ne_one norm_u

theorem plane_unit_sphere_perfect : PerfectSpace (Metric.sphere (0 : Plane) 1) := by
  let := plane_unit_sphere_connected
  let := plane_unit_sphere_nontrivial
  infer_instance

end Unfoldings
