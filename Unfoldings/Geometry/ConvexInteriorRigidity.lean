module

public import Unfoldings.Basic
public import Unfoldings.Geometry.ConvexLocalRigidity
public import Mathlib.Analysis.InnerProductSpace.Convex

/-! Local rigid coordinates on a convex cell interior extend to its whole closed cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {s : Set Plane} (convex : Convex ℝ s) (full : (interior s).Nonempty)
  (f : s → Plane) (continuous_f : Continuous f)
  (local_isometry : ∀ x : interior s, ∃ r > 0,
    Isometry (fun y : Metric.ball x r =>
      f ⟨y.val.val, interior_subset y.val.property⟩))

include convex full continuous_f local_isometry in
/-- Interior local isometries determine one rigid motion, including every boundary point. -/
theorem exists_rigid_motion_of_interior_local_isometry :
    ∃ A : Plane ≃ᵃⁱ[ℝ] Plane, ∀ x : s, f x = A x.val := by
  obtain ⟨A, agrees⟩ := exists_rigid_motion_on_cell convex full
    (fun x : s => x.val) (isometry_subtype_coe (s := s))
    (interior s) isOpen_interior
    (fun x : interior s => f ⟨x.val, interior_subset x.property⟩)
    local_isometry (fun _ inside => inside)
  refine ⟨A, fun x => ?_⟩
  let inside : Set s := {x | x.val ∈ interior s}
  have near : x ∈ closure inside := by
    have ambient : x.val ∈ closure (interior s) := by
      rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
      exact subset_closure x.property
    apply Metric.mem_closure_iff.mpr
    intro ε positive
    obtain ⟨y, member, close⟩ := Metric.mem_closure_iff.mp ambient ε positive
    exact ⟨⟨y, interior_subset member⟩, member, close⟩
  have closed : IsClosed {x : s | f x = A x.val} :=
    isClosed_eq continuous_f (A.continuous.comp continuous_subtype_val)
  apply closed.closure_subset_iff.mpr _ near
  intro y hy
  exact agrees y hy

include convex full continuous_f local_isometry in
theorem isometry_of_interior_local_isometry : Isometry f := by
  obtain ⟨A, agrees⟩ := exists_rigid_motion_of_interior_local_isometry convex full f
    continuous_f local_isometry
  intro x y
  rw [agrees x, agrees y, A.isometry.edist_eq]
  rfl

end Unfoldings
