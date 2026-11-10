module

public import Unfoldings.Geometry.Shear
public import Unfoldings.Geometry.AngleMonotone

/-! Sheared strict quadrants are positive spans of two rays with angle strictly below pi/2. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def shearWedgeFirst : Plane := WithLp.toLp 2 ![1, 0]

def shearWedgeLast (t : ℝ) : Plane := WithLp.toLp 2 ![t, 1]

def shearWedgeWidth (t : ℝ) : ℝ := InnerProductGeometry.angle shearWedgeFirst (shearWedgeLast t)

theorem shearWedgeFirst_ne_zero : shearWedgeFirst ≠ 0 := by
  intro equal
  have coordinate := congrArg (fun p : Plane => p 0) equal
  norm_num [shearWedgeFirst] at coordinate

theorem shearWedgeLast_ne_zero (t : ℝ) : shearWedgeLast t ≠ 0 := by
  intro equal
  have coordinate := congrArg (fun p : Plane => p 1) equal
  norm_num [shearWedgeLast] at coordinate

theorem shearWedgeWidth_lt_pi_div_two {t : ℝ} (positive : 0 < t) :
    shearWedgeWidth t < Real.pi / 2 := by
  apply lt_of_not_ge
  intro wide
  have nonpositive := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr wide
  have scalar : inner ℝ shearWedgeFirst (shearWedgeLast t) = t := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, shearWedgeFirst, shearWedgeLast]
  rw [scalar] at nonpositive
  exact (not_lt_of_ge nonpositive) positive

theorem inDirectionWedge_of_sheared_quadrant (t : ℝ) (v : Plane)
    (inside : StrictQuadrant (quadrantShear t v)) :
    InDirectionWedge shearWedgeFirst (shearWedgeLast t) v := by
  refine ⟨v 0 - t * v 1, v 1, inside.1.le, inside.2.le, ?_⟩
  ext i
  fin_cases i
  · change v 0 = (v 0 - t * v 1) * 1 + v 1 * t
    ring
  · change v 1 = (v 0 - t * v 1) * 0 + v 1 * 1
    ring

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

theorem angleMonotone_of_sheared_quadrant (t : ℝ)
    (directions : ∀ i, StrictQuadrant (quadrantShear t (P.edge i))) :
    P.AngleMonotone (shearWedgeWidth t) :=
  ⟨shearWedgeFirst, shearWedgeLast t, shearWedgeFirst_ne_zero, shearWedgeLast_ne_zero t, le_rfl,
    fun i => inDirectionWedge_of_sheared_quadrant t (P.edge i) (directions i)⟩

theorem radiallyMonotone_of_sheared_quadrant {t : ℝ} (positive : 0 < t)
    (directions : ∀ i, StrictQuadrant (quadrantShear t (P.edge i))) : P.RadiallyMonotone :=
  AngleMonotone.radiallyMonotone P (P.angleMonotone_of_sheared_quadrant t directions)
    (shearWedgeWidth_lt_pi_div_two positive).le

end PolygonalChain
end Unfoldings
