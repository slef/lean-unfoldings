module

public import Unfoldings.Geometry.CornerSpan
public import Unfoldings.Topology.Quadrant
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-! Centered affine half-plane coordinates at the interior of a triangle edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

open PlanarTopology

def edgeCoordinates (T : Triangle) (e : Fin 3) (x : T.Edge e) : Plane ≃ₜ (ℝ × ℝ) :=
  (T.cornerCombinationHomeomorph e).symm.trans
    (Homeomorph.subRight (T.coord (next e) x.val, (0 : ℝ)))

@[simp] theorem edgeCoordinates_apply (T : Triangle) (e : Fin 3) (x : T.Edge e) (p : Plane) :
    T.edgeCoordinates e x p =
      (T.coord (next e) p - T.coord (next e) x.val, T.coord (next (next e)) p) := by
  change (T.coord (next e) p, T.coord (next (next e)) p) -
    (T.coord (next e) x.val, (0 : ℝ)) = _
  exact Prod.ext rfl (sub_zero _)

@[simp] theorem edgeCoordinates_center (T : Triangle) (e : Fin 3) (x : T.Edge e) :
    T.edgeCoordinates e x x.val = (0, 0) := by
  rw [edgeCoordinates_apply, sub_self, T.coord_edge_eq_zero e x]

def edgeHalfBallHomeomorph (T : Triangle) (e : Fin 3) (x : T.Edge e) (r : ℝ) :
    T.edgeHalfBall e x r ≃ₜ
      (Subtype.val ⁻¹' (T.edgeCoordinates e x '' Metric.ball x.val r) : Set closedHalfPlane) where
  toFun p := ⟨⟨T.edgeCoordinates e x p.val, by
    change 0 ≤ (T.edgeCoordinates e x p.val).2
    have height : 0 ≤ T.coord (next (next e)) p.val := p.property.2
    simpa only [edgeCoordinates_apply] using height⟩,
    p.val, p.property.1, rfl⟩
  invFun p := ⟨(T.edgeCoordinates e x).symm p.val.val, by
    constructor
    · obtain ⟨y, hy, equal⟩ := p.property
      rw [← equal, Homeomorph.symm_apply_apply]
      exact hy
    · have coordinates := (T.edgeCoordinates e x).apply_symm_apply p.val.val
      have height := congrArg Prod.snd coordinates
      rw [edgeCoordinates_apply] at height
      change T.coord (next (next e)) ((T.edgeCoordinates e x).symm p.val.val) =
        p.val.val.2 at height
      change 0 ≤ T.coord (next (next e)) ((T.edgeCoordinates e x).symm p.val.val)
      rw [height]
      exact p.val.property⟩
  left_inv p := Subtype.ext ((T.edgeCoordinates e x).symm_apply_apply _)
  right_inv p := Subtype.ext (Subtype.ext ((T.edgeCoordinates e x).apply_symm_apply _))
  continuous_toFun := by fun_prop
  continuous_invFun :=
    ((T.edgeCoordinates e x).symm.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem edgeHalfBallHomeomorph_open_target (T : Triangle) (e : Fin 3) (x : T.Edge e) (r : ℝ) :
    IsOpen (Subtype.val ⁻¹' (T.edgeCoordinates e x '' Metric.ball x.val r) : Set closedHalfPlane) :=
  ((T.edgeCoordinates e x).isOpenMap _ Metric.isOpen_ball).preimage continuous_subtype_val

end Unfoldings.Triangle
