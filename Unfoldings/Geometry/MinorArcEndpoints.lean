module

public import Unfoldings.Geometry.MinorArcCone
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A closed minor arc with a specified first endpoint determines its second endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings

private theorem unit_eq_of_nonnegative_smul {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {a : ℝ} (ha : 0 ≤ a) (eq : v = a • u) : v = u := by
  rw [eq, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg ha] at hv
  rw [eq, hv, one_smul]

private theorem independent_of_minorArc_endpoints {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (distinct : u ≠ v) (nonantipodal : u + v ≠ 0) : LinearIndependent ℝ ![u, v] := by
  apply linearIndependent_fin2.mpr
  refine ⟨norm_ne_zero_iff.mp (hv.trans_ne one_ne_zero), ?_⟩
  intro a eq
  change a • v = u at eq
  rcases le_or_gt 0 a with nonnegative | negative
  · exact distinct (unit_eq_of_nonnegative_smul hv hu nonnegative eq.symm)
  · have magnitude : |a| = 1 := by
      rw [← eq, norm_smul, hv, mul_one, Real.norm_eq_abs] at hu
      exact hu
    rw [abs_of_neg negative, neg_eq_iff_eq_neg] at magnitude
    exact nonantipodal (by rw [← eq, magnitude, neg_smul, one_smul, neg_add_cancel])

/-- Closed minor arcs with the same first endpoint have the same second
endpoint when their point sets agree and both arcs are nondegenerate. -/
theorem closedMinorArc_right_eq_of_same {u v w : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (uv : u ≠ v) (_uw : u ≠ w) (auv : u + v ≠ 0) (auw : u + w ≠ 0)
    (same : closedMinorArc u v = closedMinorArc u w) : v = w := by
  have vw : v ∈ closedMinorArc u w :=
    same ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have wv : w ∈ closedMinorArc u v :=
    same.symm ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  obtain ⟨_, a, b, ap, bp, w_eq⟩ :=
    (mem_closedMinorArc_iff_nonnegative_combination hu hv auv).mp wv
  obtain ⟨_, c, d, cp, dp, v_eq⟩ :=
    (mem_closedMinorArc_iff_nonnegative_combination hu hw auw).mp vw
  have d_pos : 0 < d := by
    apply lt_of_le_of_ne dp
    intro zero
    rw [← zero, zero_smul, add_zero] at v_eq
    exact uv ((unit_eq_of_nonnegative_smul hu hv cp v_eq).symm)
  have linear : (c + d * a) • u + (d * b - 1) • v = 0 := by
    calc
      _ = (c • u + d • w) - v := by rw [w_eq]; module
      _ = 0 := by rw [← v_eq, sub_self]
  have independent := independent_of_minorArc_endpoints hu hv uv auv
  have vanish := Fintype.linearIndependent_iff.mp independent ![c + d * a, d * b - 1]
    (by rw [Fin.sum_univ_two]; exact linear)
  have sum_zero : c + d * a = 0 := vanish 0
  have a_zero : a = 0 := by
    by_contra h
    have pos : 0 < a := lt_of_le_of_ne ap (Ne.symm h)
    exact (add_pos_of_nonneg_of_pos cp (mul_pos d_pos pos)).ne' sum_zero
  rw [a_zero, zero_smul, zero_add] at w_eq
  exact (unit_eq_of_nonnegative_smul hv hw bp w_eq).symm

end Unfoldings
