module

public import Unfoldings.Cap.RoofExtension

/-!
# The unbounded convex solid bounded above by the actual roof

The roof is exactly the frontier of the intersection of the original supporting
halfspaces. This identifies the geometric extension with an actual unbounded
convex polyhedron, rather than only a formal graph of a height function.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def roofSolid : Set Space :=
  {z | ∀ f, inner ℝ (K.normal f) z ≤ inner ℝ (K.normal f) (K.folding.place f 0)}

theorem support_halfspace_iff (f : Face) (z : Space) :
    inner ℝ (K.normal f) z ≤ inner ℝ (K.normal f) (K.folding.place f 0) ↔
      z 2 ≤ K.supportHeight f (Cap.horizontal z) := by
  rw [K.supportHeight_apply, le_div_iff₀ (K.normal_upward f)]
  have split := Cap.horizontal_inner (K.normal f) z
  constructor <;> intro bound <;> linarith

theorem mem_roofSolid_iff (z : Space) :
    z ∈ K.roofSolid ↔ z 2 ≤ K.roofHeight (Cap.horizontal z) := by
  constructor
  · intro member
    obtain ⟨f, active⟩ := K.exists_roofHeight_eq_supportHeight (Cap.horizontal z)
    rw [active]
    exact (K.support_halfspace_iff f z).mp (member f)
  · intro member f
    exact (K.support_halfspace_iff f z).mpr
      (member.trans (K.roofHeight_le_supportHeight _ f))

theorem roofSolid_eq_iInter : K.roofSolid = ⋂ f,
    (innerSL ℝ (K.normal f)) ⁻¹' Set.Iic (inner ℝ (K.normal f) (K.folding.place f 0)) := by
  ext z
  simp only [roofSolid, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic,
    innerSL_apply_apply]

theorem isClosed_roofSolid : IsClosed K.roofSolid := by
  rw [K.roofSolid_eq_iInter]
  exact isClosed_iInter (fun f => isClosed_Iic.preimage (innerSL ℝ (K.normal f)).continuous)

theorem convex_roofSolid : Convex ℝ K.roofSolid := by
  rw [K.roofSolid_eq_iInter]
  exact convex_iInter (fun f =>
    (convex_Iic _).linear_preimage (innerSL ℝ (K.normal f)).toLinearMap)

theorem below_roof_mem_interior {z : Space}
    (below : z 2 < K.roofHeight (Cap.horizontal z)) : z ∈ interior K.roofSolid := by
  let belowSet : Set Space := {z | z 2 < K.roofHeight (Cap.horizontal z)}
  have opens : IsOpen belowSet := isOpen_lt (EuclideanSpace.proj 2).continuous
    (K.continuous_roofHeight.comp Cap.horizontalCLM.continuous)
  have subset : belowSet ⊆ K.roofSolid := fun x hx => (K.mem_roofSolid_iff x).mpr hx.le
  have inside_below : z ∈ interior belowSet := by
    rw [opens.interior_eq]
    exact below
  exact interior_mono subset inside_below

/-- The actual extended roof is precisely the boundary of the convex supporting-halfspace solid. -/
theorem frontier_roofSolid : frontier K.roofSolid = K.extendedRoof := by
  ext z
  constructor
  · intro boundary
    have member := K.isClosed_roofSolid.closure_eq ▸ boundary.1
    have below := (K.mem_roofSolid_iff z).mp member
    apply le_antisymm below
    by_contra strict
    exact boundary.2 (K.below_roof_mem_interior (lt_of_not_ge strict))
  · intro roof
    have equal : z 2 = K.roofHeight (Cap.horizontal z) := roof
    refine ⟨subset_closure ((K.mem_roofSolid_iff z).mpr equal.le), ?_⟩
    intro interior_point
    obtain ⟨ε, positive, inside⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp interior_point)
    let above : Space := z + EuclideanSpace.single 2 (ε / 2)
    have near : dist above z < ε := by
      rw [dist_eq_norm]
      change ‖(z + EuclideanSpace.single 2 (ε / 2)) - z‖ < ε
      rw [add_sub_cancel_left, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have above_member := (K.mem_roofSolid_iff above).mp (inside near)
    have horizontal : Cap.horizontal above = Cap.horizontal z := by
      ext i
      fin_cases i <;> simp [above, Cap.horizontal_apply, EuclideanSpace.single]
    have vertical : above 2 = z 2 + ε / 2 := by
      simp [above, EuclideanSpace.single]
    rw [horizontal, vertical, equal] at above_member
    linarith

end Unfoldings.ConvexCap
