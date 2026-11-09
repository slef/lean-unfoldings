module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local rigid face patches determine locally constant motions

Every neighborhood of a point of a full-dimensional convex set contains
interior points. Hence two affine motions agreeing on a neighborhood within
that set agree globally. Rigid patches representing the same coordinates
therefore have locally constant motions, including at boundary centers.
-/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rigid_eq_on_convex_patch {s : Set E} (convex : Convex ℝ s)
    (interior_nonempty : (interior s).Nonempty) {x : E} (inside : x ∈ s)
    {r : ℝ} (positive : 0 < r) (A B : E ≃ᵃⁱ[ℝ] E)
    (agrees : ∀ y ∈ s, dist y x < r → A y = B y) : A = B := by
  have in_closure : x ∈ closure (interior s) := by
    rw [convex.closure_interior_eq_closure_of_nonempty_interior interior_nonempty]
    exact subset_closure inside
  obtain ⟨y, in_interior, close⟩ := Metric.mem_closure_iff.mp in_closure r positive
  have patch_interior : (interior (s ∩ Metric.ball x r)).Nonempty := by
    refine ⟨y, ?_⟩
    rw [interior_inter, Metric.isOpen_ball.interior_eq]
    exact ⟨in_interior, by simpa only [Metric.mem_ball, dist_comm] using close⟩
  have equal : A.toAffineMap = B.toAffineMap := AffineMap.ext_on
    (isOpen_interior.affineSpan_eq_top patch_interior) (by
      intro z hz
      have member := interior_subset hz
      exact agrees z member.1 member.2)
  ext z
  exact congrArg (fun f : E →ᵃ[ℝ] E => f z) equal

structure LocalRigidPatch {s : Set E} (U : Set s) (coordinates : U → E) (x : U) where
  radius : ℝ
  positive : 0 < radius
  place : E ≃ᵃⁱ[ℝ] E
  inside : ∀ y : s, dist y.val x.val.val < radius → y ∈ U
  agrees : ∀ y : U, dist y.val.val x.val.val < radius → coordinates y = place y.val.val

theorem localRigidPatch_motion_locallyConstant {s : Set E} (convex : Convex ℝ s)
    (interior_nonempty : (interior s).Nonempty) {U : Set s} {coordinates : U → E}
    (patch : ∀ x : U, LocalRigidPatch U coordinates x) :
    IsLocallyConstant (fun x => (patch x).place) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [Metric.ball_mem_nhds x (patch x).positive] with y near
  have close : dist y.val.val x.val.val < (patch x).radius := near
  let r := min (patch y).radius ((patch x).radius - dist y.val.val x.val.val) / 2
  have positive_r : 0 < r := half_pos (lt_min (patch y).positive (sub_pos.mpr close))
  have small_y : r < (patch y).radius := by
    have upper := min_le_left (patch y).radius ((patch x).radius - dist y.val.val x.val.val)
    dsimp [r]
    linarith [(patch y).positive]
  have small_x : r < (patch x).radius - dist y.val.val x.val.val := by
    have upper := min_le_right (patch y).radius ((patch x).radius - dist y.val.val x.val.val)
    dsimp [r]
    linarith
  apply rigid_eq_on_convex_patch convex interior_nonempty y.val.property positive_r
  intro z hz near_z
  let w : U := ⟨⟨z, hz⟩, (patch y).inside ⟨z, hz⟩ (near_z.trans small_y)⟩
  have near_x : dist z x.val.val < (patch x).radius := by
    have triangle := dist_triangle z y.val.val x.val.val
    linarith
  exact ((patch y).agrees w (near_z.trans small_y)).symm.trans ((patch x).agrees w near_x)

end Unfoldings
