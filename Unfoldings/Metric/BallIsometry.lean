module

public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Isometries restricted to balls with named centers

The radius is arbitrary, including zero and infinity. Recording the center
equality explicitly makes whole-ball chart composition independent of a
particular choice of normalized coordinates.
-/

@[expose] public section

open scoped ENNReal

namespace Unfoldings

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

def basedEBallIsometry (e : X ≃ᵢ Y) (a : X) (b : Y) (center : e a = b) (r : ℝ≥0∞) :
    Metric.eball a r ≃ᵢ Metric.eball b r where
  toFun x := ⟨e x.val, by
    change edist (e x.val) b < r
    rw [← center, e.isometry.edist_eq]
    exact x.property⟩
  invFun y := ⟨e.symm y.val, by
    have equal : edist (e.symm y.val) a = edist y.val b := by
      rw [← e.isometry.edist_eq (e.symm y.val) a, e.apply_symm_apply, center]
    change edist (e.symm y.val) a < r
    rw [equal]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  isometry_toFun x y := e.isometry x.val y.val

@[simp] theorem basedEBallIsometry_apply (e : X ≃ᵢ Y) (a : X) (b : Y)
    (center : e a = b) (r : ℝ≥0∞) (x : Metric.eball a r) :
    (basedEBallIsometry e a b center r x).val = e x.val := rfl

@[simp] theorem basedEBallIsometry_symm_apply (e : X ≃ᵢ Y) (a : X) (b : Y)
    (center : e a = b) (r : ℝ≥0∞) (y : Metric.eball b r) :
    ((basedEBallIsometry e a b center r).symm y).val = e.symm y.val := rfl

end Unfoldings
