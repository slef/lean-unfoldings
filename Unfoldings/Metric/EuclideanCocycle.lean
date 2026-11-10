module

public import Unfoldings.Metric.EuclideanAtlas

/-! The rigid germs of Euclidean metric chart transitions satisfy the exact cocycle laws. -/

@[expose] public section

noncomputable section

namespace Unfoldings.EuclideanAtlas

variable {X : Type*} [MetricSpace X] (A : EuclideanAtlas X)

theorem transition_self (i x : X) (member : x ∈ (A i).domain) :
    A.transition i i x = AffineIsometryEquiv.refl ℝ Plane := by
  let P := A.transitionPatch i i x ⟨member, member⟩
  let Q : A.TransitionPatch i i x :=
    { P with motion := AffineIsometryEquiv.refl ℝ Plane, agrees := fun _ => rfl }
  rw [A.transition_eq i i x ⟨member, member⟩]
  exact P.motion_unique Q

theorem transition_comp (i j k x : X)
    (member : x ∈ (A i).domain ∩ (A j).domain ∩ (A k).domain) :
    (A.transition i j x).trans (A.transition j k x) = A.transition i k x := by
  let P := A.transitionPatch i j x member.1
  let Q := A.transitionPatch j k x ⟨member.1.2, member.2⟩
  let R := A.transitionPatch i k x ⟨member.1.1, member.2⟩
  let composite : A.TransitionPatch i k x :=
    { radius := min P.radius Q.radius
      positive := lt_min P.positive Q.positive
      inside_left := (Metric.ball_subset_ball (min_le_left _ _)).trans P.inside_left
      inside_right := (Metric.ball_subset_ball (min_le_right _ _)).trans Q.inside_right
      motion := P.motion.trans Q.motion
      agrees := by
        intro y
        have first := P.agrees ⟨y.val, (Metric.ball_subset_ball (min_le_left _ _)) y.property⟩
        have last := Q.agrees ⟨y.val, (Metric.ball_subset_ball (min_le_right _ _)) y.property⟩
        change Q.motion (P.motion _) = _
        exact (congrArg Q.motion first).trans last }
  rw [A.transition_eq i j x member.1,
    A.transition_eq j k x ⟨member.1.2, member.2⟩,
    A.transition_eq i k x ⟨member.1.1, member.2⟩]
  exact composite.motion_unique R

theorem transition_symm (i j x : X) (member : x ∈ (A i).domain ∩ (A j).domain) :
    (A.transition i j x).symm = A.transition j i x := by
  have composite := A.transition_comp i j i x ⟨member, member.1⟩
  rw [A.transition_self i x member.1] at composite
  apply AffineIsometryEquiv.ext
  intro z
  have equal := congrArg (fun M : Plane ≃ᵃⁱ[ℝ] Plane => M ((A.transition i j x).symm z)) composite
  simpa only [AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.apply_symm_apply, AffineIsometryEquiv.coe_refl, id_eq] using equal.symm

end Unfoldings.EuclideanAtlas
