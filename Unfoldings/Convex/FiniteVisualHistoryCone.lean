module

public import Unfoldings.Convex.VisualHistoryCone
public import Unfoldings.Geometry.PlanarWedgeAngle
public import Unfoldings.Geometry.ConeBoundaryRays
public import Unfoldings.Geometry.DirectionWedgeOperations

/-! Finite visual-angle witnesses yield the exact aperture of the history cone. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry NormedSpace

private theorem planar_determinant_mul_inner (n x y : Plane) :
    inner ℝ n x * orient 0 n y - orient 0 n x * inner ℝ n y =
      (n 0 ^ 2 + n 1 ^ 2) * orient 0 x y := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    orient, PiLp.zero_apply, sub_zero]
  ring

private theorem angle_eq_zero_of_collinear_positive {n x y : Plane}
    (first : 0 < inner ℝ n x) (last : 0 < inner ℝ n y)
    (zero : orient 0 x y = 0) : angle x y = 0 := by
  have xn : x ≠ 0 := fun eq => first.ne' (by rw [eq, inner_zero_right])
  obtain ⟨t, equal⟩ := exists_lineMap_of_orient_eq_zero xn.symm zero
  rw [AffineMap.lineMap_apply_module'] at equal
  simp only [sub_zero, add_zero] at equal
  have ht : 0 < t := by
    rw [equal, real_inner_smul_right] at last
    exact pos_of_mul_pos_left last first.le
  exact angle_eq_zero_iff.mpr ⟨xn, t, ht, equal⟩

/-- Inside one open halfplane, the least and greatest coordinate ratios are
the two actual extreme rays of any finite family with positive visual angle. -/
theorem exists_finite_extremal_viewing_rays {I : Type*} [Fintype I] [Nonempty I]
    (rays : I → Plane) (n : Plane) (positive : ∀ i, 0 < inner ℝ n (rays i))
    (wide : ∃ i j, 0 < angle (rays i) (rays j)) :
    ∃ a b : I, 0 < orient 0 (rays a) (rays b) ∧
      ∀ i, InDirectionWedge (rays a) (rays b) (rays i) := by
  classical
  let ratio i := orient 0 n (rays i) / inner ℝ n (rays i)
  obtain ⟨a, _, least⟩ := Finset.exists_min_image (Finset.univ : Finset I) ratio Finset.univ_nonempty
  obtain ⟨b, _, greatest⟩ := Finset.exists_max_image (Finset.univ : Finset I) ratio
    Finset.univ_nonempty
  have n_size : 0 < n 0 ^ 2 + n 1 ^ 2 := by
    by_contra! h
    have nc0 : n 0 = 0 := by nlinarith only [h, sq_nonneg (n 1)]
    have nc1 : n 1 = 0 := by nlinarith only [h, sq_nonneg (n 0)]
    have zero : n = 0 := by ext i; fin_cases i; exact nc0; exact nc1
    have pos := positive (Classical.choice (inferInstance : Nonempty I))
    rw [zero, inner_zero_left] at pos
    exact lt_irrefl _ pos
  have sign (i j : I) : ratio i ≤ ratio j ↔ 0 ≤ orient 0 (rays i) (rays j) := by
    dsimp only [ratio]
    rw [div_le_div_iff₀ (positive i) (positive j), ← sub_nonneg]
    rw [mul_comm (orient 0 n (rays j)), planar_determinant_mul_inner]
    exact mul_nonneg_iff_of_pos_left n_size
  have diff : 0 < orient 0 (rays a) (rays b) := by
    apply lt_of_le_of_ne ((sign a b).mp (least b (Finset.mem_univ b)))
    intro zero
    have reverse : 0 ≤ orient 0 (rays b) (rays a) := by
      have anti : orient 0 (rays b) (rays a) = -orient 0 (rays a) (rays b) := by
        simp only [orient, PiLp.zero_apply, sub_zero]
        ring
      rw [anti, ← zero, neg_zero]
    obtain ⟨i, j, h⟩ := wide
    have e : ∀ k, ratio k = ratio a := fun k =>
      le_antisymm ((greatest k (Finset.mem_univ k)).trans ((sign b a).mpr reverse))
        (least k (Finset.mem_univ k))
    have both : orient 0 (rays i) (rays j) = 0 := by
      have s1 := (sign i j).mp ((e i).trans (e j).symm).le
      have s2 := (sign j i).mp ((e j).trans (e i).symm).le
      simp only [orient, PiLp.zero_apply, sub_zero] at s1 s2 ⊢
      linarith
    exact h.ne' (angle_eq_zero_of_collinear_positive (positive i) (positive j) both)
  refine ⟨a, b, diff, fun i => ?_⟩
  have first := (sign i b).mp (greatest i (Finset.mem_univ i))
  have last := (sign a i).mp (least i (Finset.mem_univ i))
  have balance := orient_zero_balance (rays a) (rays i) (rays b)
  have equation := congrArg (fun x : Plane => (orient 0 (rays a) (rays b))⁻¹ • x) balance
  exact ⟨_, _, div_nonneg first diff.le, div_nonneg last diff.le,
    by simpa only [smul_add, smul_smul, div_eq_inv_mul, inv_mul_cancel₀ diff.ne', one_smul]
      using equation⟩

namespace SlopeEnvelope

/-- Vertex bounds certify the actual angular history cone of their convex hull. -/
theorem exists_historyCone_angle_of_vertex_bounds {I : Type*} [Finite I] [Nonempty I]
    (body : I → Plane) (p normal : Plane) (inside : ∀ i, 0 < inner ℝ normal (p - body i))
    {lower upper : ℝ} (lower_nonneg : 0 ≤ lower) (upper_pi : upper ≤ Real.pi)
    (lower_bound : ∃ i j, lower < angle (p - body i) (p - body j))
    (upper_bound : ∀ i j, i ≠ j → angle (p - body i) (p - body j) < upper) :
    ∃ (axis : Plane) (width : ℝ),
      axis ≠ 0 ∧ Real.pi - upper < width ∧ width < Real.pi - lower ∧
      ∀ z : Plane, z ≠ 0 → (z ∈ historyCone (convexHull ℝ (Set.range body)) p ↔
        angle axis z ≤ width / 2) := by
  let := Fintype.ofFinite I
  let rays i := p - body i
  obtain ⟨i, j, lo⟩ := lower_bound
  obtain ⟨a, b, ccw, encloses⟩ := exists_finite_extremal_viewing_rays rays normal inside
    ⟨i, j, lower_nonneg.trans_lt lo⟩
  have ne (k : I) : rays k ≠ 0 := fun eq => (inside k).ne' (by rw [show p - body k = 0 from eq,
    inner_zero_right])
  have distinct : a ≠ b := by
    rintro rfl
    exact ccw.ne' (by simp only [orient, PiLp.zero_apply, sub_zero]; ring)
  have extreme_lo : lower < angle (rays a) (rays b) :=
    lo.trans_le (angle_le_angle_of_inDirectionWedge (ne i) (ne j) (encloses i) (encloses j))
  have extreme_hi := upper_bound a b distinct
  let u := normalize (rays a)
  let v := normalize (rays b)
  have u_unit : ‖u‖ = 1 := norm_normalize (ne a)
  have v_unit : ‖v‖ = 1 := norm_normalize (ne b)
  have adjusted : angle u v = angle (rays a) (rays b) := by
    dsimp only [u, v, NormedSpace.normalize]
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr (ne a))),
      angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr (ne b)))]
  have u_back : ‖rays a‖ • u = rays a := norm_smul_normalize _
  have v_back : ‖rays b‖ • v = rays b := norm_smul_normalize _
  have vertex_wedge (k : I) : InDirectionWedge u v (rays k) := by
    obtain ⟨s, t, sn, tn, eq⟩ := encloses k
    refine ⟨s * ‖rays a‖, t * ‖rays b‖, mul_nonneg sn (norm_nonneg _),
      mul_nonneg tn (norm_nonneg _), ?_⟩
    rw [← smul_smul, ← smul_smul, u_back, v_back]
    exact eq
  let L := convexHull ℝ (Set.range body)
  have hull_wedge : ∀ w ∈ L, InDirectionWedge u v (p - w) := by
    apply show L ⊆ {w | InDirectionWedge u v (p - w)} from ?_
    apply convexHull_min
    · rintro _ ⟨k, rfl⟩
      exact vertex_wedge k
    · let f : Plane →ᵃ[ℝ] Plane := {
        toFun := fun w => p - w
        linear := -LinearMap.id
        map_vadd' := by intro x y; simp; module }
      exact (convex_inDirectionWedge u v).affine_preimage f
  have axis : u + v ≠ 0 := by
    intro zero
    have neg : v = (-1 : ℝ) • u := by rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_right zero
    have angle_pi := angle_eq_pi_iff.mpr ⟨norm_ne_zero_iff.mp (by simp [u_unit] : ‖u‖ ≠ 0),
      -1, by norm_num, neg⟩
    rw [← adjusted, angle_pi] at extreme_hi
    exact not_lt_of_ge upper_pi extreme_hi
  refine ⟨u + v, Real.pi - angle u v, axis, ?_, ?_, ?_⟩
  · rw [adjusted]
    linarith only [extreme_hi]
  · rw [adjusted]
    linarith only [extreme_lo]
  · intro z zn
    exact historyCone_iff_angle_of_extremal_rays u_unit v_unit
      (adjusted ▸ lower_nonneg.trans_lt extreme_lo) (adjusted ▸ extreme_hi.trans_le upper_pi)
      ⟨body a, subset_convexHull ℝ _ ⟨a, rfl⟩, ‖rays a‖, norm_pos_iff.mpr (ne a), u_back.symm⟩
      ⟨body b, subset_convexHull ℝ _ ⟨b, rfl⟩, ‖rays b‖, norm_pos_iff.mpr (ne b), v_back.symm⟩
      hull_wedge zn

end SlopeEnvelope
end Unfoldings
