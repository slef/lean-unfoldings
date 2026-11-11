module

public import Unfoldings.Basic
public import Unfoldings.Geometry.AngleMonotone

/-!
# Coordinate monotonicity of acute angle-monotone chains

An acute pair of planar banks has a common coordinate sign. Hence every chain
in their positive span is monotone in at least one ambient coordinate. The
claim is preserved in every orthogonal frame and after translation.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem acute_banks_common_coordinate_sign (u v : Plane) (acute : 0 < inner ℝ u v) :
    (0 ≤ u 0 ∧ 0 ≤ v 0) ∨ (u 0 ≤ 0 ∧ v 0 ≤ 0) ∨
      (0 ≤ u 1 ∧ 0 ≤ v 1) ∨ (u 1 ≤ 0 ∧ v 1 ≤ 0) := by
  have split : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  rw [split] at acute
  by_cases first : 0 < u 0 * v 0
  · rcases mul_pos_iff.mp first with positive | negative
    · exact Or.inl ⟨positive.1.le, positive.2.le⟩
    · exact Or.inr (Or.inl ⟨negative.1.le, negative.2.le⟩)
  · have last : 0 < u 1 * v 1 := by linarith
    rcases mul_pos_iff.mp last with positive | negative
    · exact Or.inr (Or.inr (Or.inl ⟨positive.1.le, positive.2.le⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨negative.1.le, negative.2.le⟩))

theorem InDirectionWedge.coordinate_nonneg {u v x : Plane} (inside : InDirectionWedge u v x)
    (i : Fin 2) (first : 0 ≤ u i) (last : 0 ≤ v i) : 0 ≤ x i := by
  obtain ⟨a, b, ha, hb, rfl⟩ := inside
  change 0 ≤ a * u i + b * v i
  exact add_nonneg (mul_nonneg ha first) (mul_nonneg hb last)

theorem InDirectionWedge.coordinate_nonpos {u v x : Plane} (inside : InDirectionWedge u v x)
    (i : Fin 2) (first : u i ≤ 0) (last : v i ≤ 0) : x i ≤ 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := inside
  change a * u i + b * v i ≤ 0
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha first)
    (mul_nonpos_of_nonneg_of_nonpos hb last)

namespace PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

/-- The same actual chain in a translated orthogonal frame. -/
def inFrame (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) : PolygonalChain Plane n where
  vertex i := L (P.vertex i - center)

@[simp] theorem inFrame_edge (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) (i : Fin n) :
    (P.inFrame L center).edge i = L (P.edge i) := by
  change L (P.vertex i.succ - center) - L (P.vertex i.castSucc - center) =
    L (P.vertex i.succ - P.vertex i.castSucc)
  rw [← map_sub]
  congr 1
  abel

theorem AngleMonotone.inFrame {width : ℝ} (monotone : P.AngleMonotone width)
    (L : Plane ≃ₗᵢ[ℝ] Plane) (center : Plane) : (P.inFrame L center).AngleMonotone width := by
  obtain ⟨u, v, une, vne, angle, directions⟩ := monotone
  refine ⟨L u, L v, ?_, ?_, ?_, fun i => ?_⟩
  · simpa only [map_zero] using L.injective.ne une
  · simpa only [map_zero] using L.injective.ne vne
  · exact (L.toLinearIsometry.angle_map u v).le.trans angle
  · obtain ⟨a, b, ha, hb, equal⟩ := directions i
    refine ⟨a, b, ha, hb, ?_⟩
    rw [P.inFrame_edge, equal, map_add, map_smul, map_smul]

theorem coordinate_monotone_of_acute_wedge (u v : Plane) (acute : 0 < inner ℝ u v)
    (directions : ∀ i, InDirectionWedge u v (P.edge i)) :
    Monotone (fun i => P.vertex i 0) ∨ Antitone (fun i => P.vertex i 0) ∨
      Monotone (fun i => P.vertex i 1) ∨ Antitone (fun i => P.vertex i 1) := by
  rcases acute_banks_common_coordinate_sign u v acute with first | first | last | last
  · left
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact sub_nonneg.mp ((directions i).coordinate_nonneg 0 first.1 first.2)
  · right; left
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    exact sub_nonpos.mp ((directions i).coordinate_nonpos 0 first.1 first.2)
  · right; right; left
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact sub_nonneg.mp ((directions i).coordinate_nonneg 1 last.1 last.2)
  · right; right; right
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    exact sub_nonpos.mp ((directions i).coordinate_nonpos 1 last.1 last.2)

/-- Acuteness gives an ambient monotone coordinate in every orthogonal frame. -/
theorem AngleMonotone.coordinate_monotone {width : ℝ} (monotone : P.AngleMonotone width)
    (small : width < Real.pi / 2) :
    Monotone (fun i => P.vertex i 0) ∨ Antitone (fun i => P.vertex i 0) ∨
      Monotone (fun i => P.vertex i 1) ∨ Antitone (fun i => P.vertex i 1) := by
  obtain ⟨u, v, _une, _vne, angle, directions⟩ := monotone
  have acute : 0 < inner ℝ u v := by
    by_contra nonpositive
    have wide := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp
      (le_of_not_gt nonpositive)
    exact not_lt_of_ge wide (angle.trans_lt small)
  exact P.coordinate_monotone_of_acute_wedge u v acute directions

end PolygonalChain
end Unfoldings
