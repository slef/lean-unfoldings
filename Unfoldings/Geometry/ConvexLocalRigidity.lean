module

public import Unfoldings.Geometry.ConvexRigidity
public import Unfoldings.Geometry.ConvexPatchRigidity

/-! Local isometries pulled back to a convex cell give actual rigid face patches. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [StrictConvexSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E}

/-- The cell may meet the local isometry region along its boundary as well as its interior. -/
theorem exists_localRigidPatch (convex : Convex ℝ s) (full : (interior s).Nonempty)
    (fold : s → X) (fold_isometry : Isometry fold) (U : Set X) (open_U : IsOpen U)
    (coordinates : U → E)
    (local_isometry : ∀ x : U, ∃ r > 0,
      Isometry (fun y : Metric.ball x r => coordinates y.val))
    (x : {y : s | fold y ∈ U}) :
    Nonempty (LocalRigidPatch {y : s | fold y ∈ U}
      (fun y => coordinates ⟨fold y.val, y.property⟩) x) := by
  obtain ⟨r, positive, isometry⟩ := local_isometry ⟨fold x.val, x.property⟩
  obtain ⟨a, apos, inside⟩ := Metric.isOpen_iff.mp (open_U.preimage fold_isometry.continuous)
    x.val x.property
  let radius := min a r
  have radius_pos : 0 < radius := lt_min apos positive
  let patch := s ∩ Metric.ball x.val.val radius
  let point (y : patch) : s := ⟨y.val, y.property.1⟩
  have in_U (y : patch) : fold (point y) ∈ U :=
    inside (show point y ∈ Metric.ball x.val a from
      (Metric.mem_ball.mp y.property.2).trans_le (min_le_left _ _))
  let lift (y : patch) : Metric.ball (⟨fold x.val, x.property⟩ : U) r :=
    ⟨⟨fold (point y), in_U y⟩, by
      change dist (fold (point y)) (fold x.val) < r
      rw [fold_isometry.dist_eq]
      exact (Metric.mem_ball.mp y.property.2).trans_le (min_le_right _ _)⟩
  have lift_isometry : Isometry lift := fun y z => fold_isometry (point y) (point z)
  have interior_patch : (interior patch).Nonempty := by
    have closure : x.val.val ∈ closure (interior s) := by
      rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
      exact subset_closure x.val.property
    obtain ⟨y, member, near⟩ := Metric.mem_closure_iff.mp closure radius radius_pos
    refine ⟨y, ?_⟩
    rw [interior_inter, Metric.isOpen_ball.interior_eq]
    exact ⟨member, by simpa only [Metric.mem_ball, dist_comm] using near⟩
  obtain ⟨A, agrees⟩ := exists_rigid_extension_convex (convex.inter (convex_ball _ _))
    interior_patch ((fun y => coordinates y.val) ∘ lift) (isometry.comp lift_isometry)
  refine ⟨{ radius := radius
            positive := radius_pos
            place := A
            inside := ?_
            agrees := ?_ }⟩
  · intro y near
    exact inside (show y ∈ Metric.ball x.val a from near.trans_le (min_le_left _ _))
  · intro y near
    exact (agrees ⟨y.val.val, y.val.property, near⟩).symm


/-- If an open region contains the whole cell interior, its local face motions coincide. -/
theorem exists_rigid_motion_on_cell (convex : Convex ℝ s) (full : (interior s).Nonempty)
    (fold : s → X) (fold_isometry : Isometry fold) (U : Set X) (open_U : IsOpen U)
    (coordinates : U → E)
    (local_isometry : ∀ x : U, ∃ r > 0,
      Isometry (fun y : Metric.ball x r => coordinates y.val))
    (interior_inside : ∀ y : s, y.val ∈ interior s → fold y ∈ U) :
    ∃ A : E ≃ᵃⁱ[ℝ] E, ∀ y : s, ∀ member : fold y ∈ U,
      coordinates ⟨fold y, member⟩ = A y.val := by
  let V : Set s := {y | fold y ∈ U}
  let c : V → E := fun y => coordinates ⟨fold y.val, y.property⟩
  have image_connected : IsPreconnected (Subtype.val '' V) := by
    apply convex.interior.isPreconnected.subset_closure
    · intro y inside
      exact ⟨⟨y, interior_subset inside⟩, interior_inside _ inside, rfl⟩
    · rintro _ ⟨y, _, rfl⟩
      rw [convex.closure_interior_eq_closure_of_nonempty_interior full]
      exact subset_closure y.property
  have connected : IsPreconnected V :=
    (Topology.IsInducing.subtypeVal.isPreconnected_image).mp image_connected
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp connected
  have patches (x : V) : Nonempty (LocalRigidPatch V c x) :=
    exists_localRigidPatch convex full fold fold_isometry U open_U coordinates local_isometry x
  let patch (x : V) := Classical.choice (patches x)
  have constant := localRigidPatch_motion_locallyConstant convex full patch
  obtain ⟨p, hp⟩ := full
  let root : V := ⟨⟨p, interior_subset hp⟩, interior_inside _ hp⟩
  refine ⟨(patch root).place, ?_⟩
  intro y member
  let q : V := ⟨y, member⟩
  have same := constant.apply_eq_of_preconnectedSpace q root
  have agrees := (patch q).agrees q (by simpa only [dist_self] using (patch q).positive)
  exact agrees.trans (congrArg (fun M : E ≃ᵃⁱ[ℝ] E => M y.val) same)

end Unfoldings
