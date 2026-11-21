module

public import Unfoldings.FewestNets.CheckedVisualSide
public import Unfoldings.FewestNets.VisualLensSupport

/-! A verified test for containment of a forbidden lens inside one polygon side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open InnerProductGeometry Real

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The lens centered at the midpoint of the witness pair. -/
def visualLensValue (c : ℝ) (p u v : Plane) : ℝ :=
  inner ℝ (p - u) (p - v) + c * |certificateOrientation.areaForm (p - u) (p - v)|

/-- Test one side for a strict upper bound on the lens support, using the
endpoint formula when its sufficient inequality is checked. -/
def checkLensSupport {D : ℕ} (hD : 0 < D) {c offset : ℝ} {u v n : Plane}
    (coef : CheckedReal D c) (cu : CheckedPlane D u) (cv : CheckedPlane D v)
    (normal : CheckedPlane D n) (limit : CheckedReal D offset) : Bool :=
  let half : CheckedReal D (1 / 2 : ℝ) := (CheckedReal.rat D (1 / 2)).convert (by norm_num)
  let one : CheckedReal D (1 : ℝ) := (CheckedReal.rat D 1).convert (by simp)
  let mid := CheckedPlane.smul hD half (CheckedPlane.add cu cv)
  let diff := CheckedPlane.smul hD half (CheckedPlane.sub cv cu)
  let midSupport := CheckedPlane.dot hD normal mid
  let A := (CheckedPlane.dot hD normal diff).abs hD
  let B := (CheckedPlane.det hD diff normal).abs hD
  if B.isLT (coef.mul hD A) then
    (midSupport.add A).isLT limit
  else
    let radius := (CheckedPlane.norm hD diff).mul hD ((one.add (coef.square hD)).sqrt hD)
    ((midSupport.add (radius.mul hD (CheckedPlane.norm hD normal))).sub
      (coef.mul hD B)).isLT limit

/-- Any point on or beyond a side giving a successful check lies outside the
closed forbidden lens. -/
theorem visualLensValue_pos_of_check {D : ℕ} (hD : 0 < D)
    {c offset : ℝ} {p u v n : Plane} (c_nonneg : 0 ≤ c) (different : u ≠ v)
    (coef : CheckedReal D c) (cu : CheckedPlane D u) (cv : CheckedPlane D v)
    (normal : CheckedPlane D n) (limit : CheckedReal D offset)
    (outside : offset ≤ inner ℝ n p)
    (tested : checkLensSupport hD coef cu cv normal limit = true) :
    0 < visualLensValue c p u v := by
  by_contra! absent
  let m := (1 / 2 : ℝ) • (u + v)
  let w := (1 / 2 : ℝ) • (v - u)
  have first : m - w = u := by dsimp [m, w]; module
  have last : m + w = v := by dsimp [m, w]; module
  have ne : w ≠ 0 := smul_ne_zero (by norm_num) (sub_ne_zero.mpr different.symm)
  have inside : inner ℝ (p - (m - w)) (p - (m + w)) +
      c * |certificateOrientation.areaForm (p - (m - w)) (p - (m + w))| ≤ 0 := by
    rwa [first, last]
  obtain ⟨disk_bound, endpoint_bound⟩ :=
    visualLens_support_bounds certificateOrientation (n := n) c_nonneg ne inside
  unfold checkLensSupport at tested
  dsimp only at tested
  split at tested
  · rename_i branch
    have close := (CheckedReal.lt_of_isLT hD _ _ branch).le
    have bound := CheckedReal.lt_of_isLT hD _ _ tested
    change |w 0 * n 1 - w 1 * n 0| ≤ c * |inner ℝ n w| at close
    rw [← areaForm_certificateOrientation] at close
    exact (not_lt_of_ge outside) ((endpoint_bound close).trans_lt bound)
  · have bound := CheckedReal.lt_of_isLT hD _ _ tested
    change inner ℝ n m + (‖w‖ * sqrt (1 + c ^ 2)) * ‖n‖ -
      c * |w 0 * n 1 - w 1 * n 0| < offset at bound
    rw [← areaForm_certificateOrientation] at bound
    exact (not_lt_of_ge outside) (disk_bound.trans_lt bound)

end Unfoldings.FewestNets
