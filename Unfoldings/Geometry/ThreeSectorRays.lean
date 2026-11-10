module

public import Unfoldings.Geometry.ThreeSectors

/-! Actual boundary rays and strict acute widths of the three near-quadrants. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def threeSectorRay (t : ℝ) : Fin 4 → Plane :=
  ![WithLp.toLp 2 ![1 - t, 1 + t], WithLp.toLp 2 ![-1, 1 - t],
    WithLp.toLp 2 ![-1, t - 1], WithLp.toLp 2 ![1 - t, -1 - t]]

def threeSectorDet (t : ℝ) (i : Fin 3) : ℝ :=
  if i = 1 then 2 * (1 - t) else 2 - t + t ^ 2

theorem threeSectorDet_pos {t : ℝ} (_nonnegative : 0 ≤ t) (small : t < 1) (i : Fin 3) :
    0 < threeSectorDet t i := by
  unfold threeSectorDet
  split_ifs <;> nlinarith only [small, sq_nonneg t]

/-- The inverse coordinate formula uses the actual two directed banks. -/
theorem threeSector_reconstruct (t : ℝ) (i : Fin 3) (v : Plane) :
    threeSectorDet t i • v =
      threeSectorCoordinates t i v 0 • threeSectorRay t i.castSucc +
      threeSectorCoordinates t i v 1 • threeSectorRay t i.succ := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [threeSectorDet, threeSectorCoordinates, threeSectorRay] <;> ring

theorem inDirectionWedge_of_closedThreeSector {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (i : Fin 3) {v : Plane} (inside : v ∈ closedThreeSector t i) :
    InDirectionWedge (threeSectorRay t i.castSucc) (threeSectorRay t i.succ) v := by
  have positive := threeSectorDet_pos nonnegative small i
  refine ⟨threeSectorCoordinates t i v 0 / threeSectorDet t i,
    threeSectorCoordinates t i v 1 / threeSectorDet t i,
    div_nonneg inside.1 positive.le, div_nonneg inside.2 positive.le, ?_⟩
  have scaled := congrArg (fun z : Plane => (threeSectorDet t i)⁻¹ • z)
    (threeSector_reconstruct t i v)
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ positive.ne', one_smul,
    div_eq_inv_mul] using scaled

theorem threeSector_banks_inner_pos {t : ℝ} (positive : 0 < t) (small : t < 1) (i : Fin 3) :
    0 < inner ℝ (threeSectorRay t i.castSucc) (threeSectorRay t i.succ) := by
  fin_cases i <;> norm_num [threeSectorRay, PiLp.inner_apply, Fin.sum_univ_two]
  all_goals nlinarith [mul_pos positive (by linarith : 0 < 1 - t)]

def threeSectorWidth (t : ℝ) (i : Fin 3) : ℝ :=
  InnerProductGeometry.angle (threeSectorRay t i.castSucc) (threeSectorRay t i.succ)

theorem threeSectorWidth_lt_pi_div_two {t : ℝ} (positive : 0 < t) (small : t < 1)
    (i : Fin 3) : threeSectorWidth t i < Real.pi / 2 := by
  apply lt_of_not_ge
  intro wide
  exact (not_lt_of_ge (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr wide))
    (threeSector_banks_inner_pos positive small i)

end Unfoldings
