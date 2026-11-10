module

public import Unfoldings.Metric.RigidChartTransition
public import Unfoldings.Metric.RigidChartUniqueness
public import Unfoldings.Metric.BallChart
public import Unfoldings.Geometry.AffineEnd
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.InnerProductSpace.Convex

/-! Open Euclidean metric charts and the unique rigid germs of their transitions. -/

@[expose] public section

open Filter Topology

noncomputable section

namespace Unfoldings

variable (X : Type*) [MetricSpace X]

structure EuclideanChartAt (x : X) where
  domain : Set X
  image : Set Plane
  chart : domain ≃ᵢ image
  open_domain : IsOpen domain
  open_image : IsOpen image
  center_mem : x ∈ domain

abbrev EuclideanAtlas := ∀ x : X, EuclideanChartAt X x

variable {X}

theorem exists_euclideanChartAt (x : X) (regular : HasMetricBallChart Plane x) :
    Nonempty (EuclideanChartAt X x) := by
  obtain ⟨D, U, open_D, member, open_U, ⟨chart⟩⟩ := regular.exists_open_chart
  exact ⟨⟨D, U, chart, open_D, open_U, member⟩⟩

def EuclideanAtlas.ofRegular (regular : ∀ x : X, HasMetricBallChart Plane x) : EuclideanAtlas X :=
  fun x => Classical.choice (exists_euclideanChartAt x (regular x))

namespace EuclideanAtlas

variable (A : EuclideanAtlas X)

structure TransitionPatch (i j x : X) where
  radius : ℝ
  positive : 0 < radius
  inside_left : Metric.ball x radius ⊆ (A i).domain
  inside_right : Metric.ball x radius ⊆ (A j).domain
  motion : Plane ≃ᵃⁱ[ℝ] Plane
  agrees : ∀ y : Metric.ball x radius,
    motion ((A i).chart ⟨y.val, inside_left y.property⟩).val =
      ((A j).chart ⟨y.val, inside_right y.property⟩).val

theorem exists_transitionPatch (i j x : X) (left : x ∈ (A i).domain)
    (right : x ∈ (A j).domain) : Nonempty (A.TransitionPatch i j x) := by
  obtain ⟨r, positive, inside_left, inside_right, motion, agrees⟩ :=
    exists_rigid_chart_transition (A i).chart (A j).chart (A i).open_domain (A j).open_domain
      (A i).open_image (A j).open_image x left right
  let M : Plane ≃ᵃⁱ[ℝ] Plane :=
    { AffineEquiv.ofBijective (φ := motion.toAffineMap)
        ⟨motion.injective, affineIsometryEnd_surjective motion⟩ with norm_map := motion.norm_map }
  exact ⟨⟨r, positive, inside_left, inside_right, M, agrees⟩⟩

namespace TransitionPatch

variable {A} {i j x : X} (P Q : A.TransitionPatch i j x)

theorem motion_unique : P.motion = Q.motion := by
  apply rigid_eq_of_agrees_in_chart (A i).chart (A i).open_domain (A i).open_image x
    (P.inside_left (Metric.mem_ball_self P.positive)) P.motion Q.motion
    (lt_min P.positive Q.positive)
  intro y near
  have first := P.agrees ⟨y.val, near.trans_le (min_le_left _ _)⟩
  have last := Q.agrees ⟨y.val, near.trans_le (min_le_right _ _)⟩
  exact first.trans last.symm

def recenter (y : X) (near : dist y x < P.radius) : A.TransitionPatch i j y where
  radius := P.radius - dist y x
  positive := sub_pos.mpr near
  inside_left z hz := P.inside_left (by
    apply Metric.mem_ball.mpr
    have bound := Metric.mem_ball.mp hz
    linarith [dist_triangle z y x])
  inside_right z hz := P.inside_right (by
    apply Metric.mem_ball.mpr
    have bound := Metric.mem_ball.mp hz
    linarith [dist_triangle z y x])
  motion := P.motion
  agrees z := P.agrees ⟨z.val, by
    apply Metric.mem_ball.mpr
    have bound := Metric.mem_ball.mp z.property
    linarith [dist_triangle z.val y x]⟩

end TransitionPatch

def transitionPatch (i j x : X) (member : x ∈ (A i).domain ∩ (A j).domain) :
    A.TransitionPatch i j x := Classical.choice (A.exists_transitionPatch i j x member.1 member.2)

def transition (i j x : X) : Plane ≃ᵃⁱ[ℝ] Plane := by
  classical
  exact if member : x ∈ (A i).domain ∩ (A j).domain then (A.transitionPatch i j x member).motion
  else AffineIsometryEquiv.refl ℝ Plane

theorem transition_eq (i j x : X) (member : x ∈ (A i).domain ∩ (A j).domain) :
    A.transition i j x = (A.transitionPatch i j x member).motion := by
  classical
  exact dite_eq_left member

theorem transition_locallyConstant (i j : X) :
    IsLocallyConstant (fun x : ↥((A i).domain ∩ (A j).domain) => A.transition i j x.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let P := A.transitionPatch i j x.val x.property
  filter_upwards [Metric.ball_mem_nhds x P.positive] with y near
  rw [A.transition_eq i j y.val y.property, A.transition_eq i j x.val x.property]
  exact (A.transitionPatch i j y.val y.property).motion_unique
    (P.recenter y.val (Metric.mem_ball.mp near))

end EuclideanAtlas
end Unfoldings
