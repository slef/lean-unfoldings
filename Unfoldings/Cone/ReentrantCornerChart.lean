module

public import Unfoldings.Cone.ReentrantSector
public import Unfoldings.Metric.PolygonalGerm
public import Unfoldings.Metric.PolygonalRigid
public import Unfoldings.Metric.BallIsometry

/-! Exact whole-ball fan charts from actual geometric corner sectors of any sub-full-turn width. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- This includes reentrant angles: every source-to-point segment stays in the actual sector. -/
theorem starConvex_closedAngularSector (width : ℝ) :
    StarConvex ℝ 0 (closedAngularSector width) := by
  rintro y ⟨r, θ, bounds, equal⟩ a b _ha hb _hab
  refine ⟨⟨b * r, mul_nonneg hb r.coe_nonneg⟩, θ, bounds, ?_⟩
  rw [smul_zero, zero_add, equal, Complex.real_smul]
  change (b : ℂ) * ((r : ℂ) * polarRay θ) = ((b * (r : ℝ) : ℝ) : ℂ) * polarRay θ
  push_cast
  ring

/-- Retain the actual physical center and oriented edge axis of a geometric corner. -/
def rigidAngularSector (frame : ℂ ≃ᵃⁱ[ℝ] ℂ) (width : ℝ) : Set ℂ :=
  frame '' closedAngularSector width

theorem starConvex_rigidAngularSector (frame : ℂ ≃ᵃⁱ[ℝ] ℂ) (width : ℝ) :
    StarConvex ℝ (frame 0) (rigidAngularSector frame width) :=
  (starConvex_closedAngularSector width).affine_image frame.toAffineMap

/-- The two genuine convex halves are isometric to the intrinsic physical corner sector. -/
def rigidSectorIsometryEquiv (frame : ℂ ≃ᵃⁱ[ℝ] ℂ) (width : ℝ)
    (positive : 0 < width) (small : width < 2 * Real.pi) :
    (bisectedSectorFan width positive small).Surface ≃ᵢ
      PolygonalPoint (rigidAngularSector frame width) :=
  (reentrantSectorIsometryEquiv width positive small).trans
    (PolygonalPoint.affineRegionIsometryEquiv frame rfl)

@[simp] theorem rigidSectorIsometryEquiv_val (frame : ℂ ≃ᵃⁱ[ℝ] ℂ) (width : ℝ)
    (positive : 0 < width) (small : width < 2 * Real.pi)
    (x : (bisectedSectorFan width positive small).Surface) :
    (rigidSectorIsometryEquiv frame width positive small x).val =
      frame ((bisectedSectorFan width positive small).develop x) := by
  change frame ((reentrantSectorIsometryEquiv width positive small x).val) = _
  rw [reentrantSectorIsometryEquiv_val]

/-- A proved geometric corner description gives a whole intrinsic fan-ball chart.
No metric-corner or local-flatness assertion is assumed, including at reentrant corners. -/
theorem exists_reentrant_corner_fan_isometry {s : Set ℂ} (x : PolygonalPoint s)
    (frame : ℂ ≃ᵃⁱ[ℝ] ℂ) (center : frame 0 = x.val) (width : ℝ)
    (positive : 0 < width) (small : width < 2 * Real.pi) {δ : ℝ} (radius : 0 < δ)
    (local_eq : ∀ z, dist z x.val < δ → (z ∈ s ↔ z ∈ rigidAngularSector frame width)) :
    ∃ A : Metric.eball x (ENNReal.ofReal (δ / 4)) ≃ᵢ
      Metric.eball (bisectedSectorFan width positive small).origin (ENNReal.ofReal (δ / 4)),
      ∀ y, frame ((bisectedSectorFan width positive small).develop (A y).val) = y.val.val := by
  let fan := bisectedSectorFan width positive small
  let E := rigidSectorIsometryEquiv frame width positive small
  have at_center : (E fan.origin).val = x.val := by
    rw [rigidSectorIsometryEquiv_val, AngularFan.develop_origin, center]
  have star : StarConvex ℝ x.val (rigidAngularSector frame width) := by
    rw [← center]
    exact starConvex_rigidAngularSector frame width
  obtain ⟨B, physical⟩ := PolygonalPoint.exists_local_starConvex_ball_isometry
    x (E fan.origin) at_center radius star local_eq
  let C := basedEBallIsometry E fan.origin (E fan.origin) rfl (ENNReal.ofReal (δ / 4))
  refine ⟨B.trans C.symm, ?_⟩
  intro y
  change frame (fan.develop (E.symm (B y).val)) = y.val.val
  rw [← rigidSectorIsometryEquiv_val frame width positive small (E.symm (B y).val)]
  change (E (E.symm (B y).val)).val = y.val.val
  rw [E.apply_symm_apply, physical]

end Unfoldings
