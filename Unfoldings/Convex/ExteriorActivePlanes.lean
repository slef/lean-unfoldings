module

public import Unfoldings.Convex.ExteriorSpatialRays

/-! Original finite supporting planes remain active on the whole positive exterior ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel)

/-- Active actual spatial support planes are exactly the original active slopes. -/
theorem plane_active_iff (i : M.Face) (x : Plane) :
    SpatialEnvelope.height M.plane x = (M.plane i).height x ↔ E.Active x i.val := by
  have equality : (M.plane i).height x = -E.affine i.val x := by
    simp only [plane, SpatialPlane.ofGraph_height, SpatialPlane.affineHeight_apply,
      SlopeEnvelope.affine, real_inner_comm x i.val]
    ring
  rw [M.height_eq, equality, neg_inj]
  exact ⟨fun active => ⟨M.included i.val i.property, active⟩, fun active => active.2⟩

end Unfoldings.SlopeEnvelope.FiniteSlopeModel

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V) (M : E.FiniteSlopeModel)

/-- The actual finite active-plane set is constant at every positive time of the whole ray. -/
theorem plane_active_ray_iff (v : V) (i : M.Face) {t : ℝ} (positive : 0 < t) :
    (SpatialEnvelope.height M.plane (R.ray v t) = (M.plane i).height (R.ray v t)) ↔
      E.Active (R.point v) i.val ∧
        inner ℝ (R.direction (R.slope v)) i.val = R.rate v := by
  rw [M.plane_active_iff]
  exact E.active_ray_iff (R.active v) rfl (R.support v) positive

/-- Choose one actual finite support active along the entire untruncated positive ray. -/
theorem exists_whole_ray_active_plane (v : V) :
    ∃ i : M.Face, E.Active (R.point v) i.val ∧
      ∀ t : ℝ, 0 < t → SpatialEnvelope.height M.plane (R.ray v t) =
        (M.plane i).height (R.ray v t) := by
  obtain ⟨i, active⟩ := AffineEnvelope.exists_height_eq (fun i => (M.plane i).height) (R.ray v 1)
  have at_one := (R.plane_active_ray_iff M v i zero_lt_one).mp active
  exact ⟨i, at_one.1, fun t positive => (R.plane_active_ray_iff M v i positive).mpr at_one⟩

end Unfoldings.SlopeEnvelope.ExteriorPlan
