module

public import Unfoldings.FewestNets.AcuteLatitudeNorthSelector

/-! The southern fan groups to the reflected copy of the same regular polar selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.AcuteLatitudeGrid

open Real Cap Module

/-- Negate the vertical coordinate of a spatial vector. -/
def flipPole (p : Space) : Space := WithLp.toLp 2 ![p 0, p 1, -p 2]

@[simp] private theorem flipPole_zero (p : Space) : flipPole p 0 = p 0 := rfl
@[simp] private theorem flipPole_one (p : Space) : flipPole p 1 = p 1 := rfl
@[simp] private theorem flipPole_two (p : Space) : flipPole p 2 = -p 2 := rfl

/-- Reflection in the equatorial plane gives the centered chart of the south pole. -/
def polarReflection : Space ≃ₗᵢ[ℝ] Space where
  toFun := flipPole
  invFun := flipPole
  left_inv p := by ext j; fin_cases j <;> simp [flipPole]
  right_inv p := by ext j; fin_cases j <;> simp [flipPole]
  map_add' p q := by
    ext j
    fin_cases j <;> simp [flipPole, PiLp.add_apply, add_comm]
  map_smul' c p := by
    ext j
    fin_cases j <;> simp [flipPole, PiLp.smul_apply, smul_eq_mul, mul_neg]
  norm_map' p := by
    change ‖flipPole p‖ = ‖p‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      Fin.sum_univ_three, flipPole_zero, flipPole_one, flipPole_two, neg_sq]

@[simp] theorem polarReflection_involutive : Function.Involutive polarReflection := polarReflection.left_inv

private theorem polarReflection_site (t lon : ℝ) :
    polarReflection (latitudeSite (π - t) lon) = latitudeSite t lon := by
  ext i
  fin_cases i
  · change sin (π - t) * cos lon = sin t * cos lon
    rw [sin_pi_sub]
  · change sin (π - t) * sin lon = sin t * sin lon
    rw [sin_pi_sub]
  · change -cos (π - t) = cos t
    rw [cos_pi_sub, neg_neg]

/-- Both extreme rows have exactly the same number of sites. -/
theorem south_rowSize_eq {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    rowSize a (stripCount a) = rowSize a 0 := by
  unfold rowSize
  rw [colatitude_last positive small, sin_pi_sub]
  simp [colatitude]

private theorem polarReflection_rowSite {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) (k : ℕ) :
    polarReflection (rowSite a (stripCount a) k) = rowSite a 0 k := by
  unfold rowSite
  rw [colatitude_last positive small, south_rowSize_eq positive small, polarReflection_site]
  simp [colatitude]

private theorem polarReflection_southPole : polarReflection (latitudeSite π 0) = latitudeSite 0 0 := by
  simpa only [sub_zero] using polarReflection_site 0 0

variable {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)

local notation "B" => chordBasis positive small
local notation "South" e => Sum.inr (Sum.inr e)

/-- The actual southern chord basis in the upward chart. -/
def southChordBasis (e : Fin (rowSize a (stripCount a))) : Basis (Fin 3) ℝ Space :=
  (B (South e)).map polarReflection.toLinearEquiv

private theorem southChordBasis_sites (e : Fin (rowSize a (stripCount a))) :
    (southChordBasis positive small e : Fin 3 → Space) =
      ![latitudeSite 0 0, rowSite a 0 e.val, rowSite a 0 (e.val + 1)] := by
  funext i
  simp only [southChordBasis, Basis.map_apply, LinearIsometryEquiv.coe_toLinearEquiv, chordBasis_apply]
  fin_cases i
  · exact polarReflection_southPole
  · exact polarReflection_rowSite positive small _
  · exact polarReflection_rowSite positive small _

private theorem southChordBasis_upward (e : Fin (rowSize a (stripCount a))) (i : Fin 3) :
    0 < southChordBasis positive small e i 2 := by
  rw [show southChordBasis positive small e i = _
    from congrFun (southChordBasis_sites positive small e) i]
  have cosine : 0 < cos (polarRadius a) := cos_pos_of_mem_Ioo
    ⟨by linarith only [polarRadius_pos positive, pi_pos],
      by linarith only [polarRadius_lt small, pi_gt_d2]⟩
  fin_cases i
  · change 0 < cos 0
    simp
  · change 0 < cos (colatitude a 0)
    simpa only [colatitude, Nat.cast_zero, zero_mul, add_zero] using cosine
  · change 0 < cos (colatitude a 0)
    simpa only [colatitude, Nat.cast_zero, zero_mul, add_zero] using cosine

private theorem southChordBasis_chart_range (e : Fin (rowSize a (stripCount a))) :
    Set.range (chordChartVertex (southChordBasis positive small e)) =
      {0, regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) e.val,
        regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) (e.val + 1)} := by
  let v := chordChartVertex (southChordBasis positive small e)
  have site := congrFun (southChordBasis_sites positive small e)
  have corner₀ : v 0 = 0 := by
    unfold v chordChartVertex
    rw [site]
    ext j
    fin_cases j <;> simp [Cap.horizontal, latitudeSite]
  have corner₁ : v 1 = regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) e.val := by
    unfold v chordChartVertex
    rw [site]
    exact north_row_gnomonic a _
  have corner₂ : v 2 = regularRingVertex polarFrame (rowSize a 0)
      (tan (polarRadius a)) (e.val + 1) := by
    unfold v chordChartVertex
    rw [site]
    exact north_row_gnomonic a _
  ext p
  change p ∈ Set.range v ↔ _
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl corner₀
    · exact Or.inr (Or.inl corner₁)
    · exact Or.inr (Or.inr corner₂)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, corner₀⟩
    · exact ⟨1, corner₁⟩
    · exact ⟨2, corner₂⟩

/-- The original southern fan is the inverse chart image of the same regular polar polygon. -/
theorem southPolarSelector_eq_chordFan :
    polarReflection ⁻¹' (gnomonicNormal '' regularSlopePolygon
      polarFrame (rowSize a 0) (tan (polarRadius a))) =
      ⋃ e : Fin (rowSize a (stripCount a)), {p : Space | ‖p‖ = 1 ∧ ∀ i, 0 ≤ (B (South e)).coord i p} := by
  have sides : 3 ≤ rowSize a 0 := le_trans (by decide : 3 ≤ 6) (polar_size_bounds positive small).1
  have radius : 0 < tan (polarRadius a) := tan_pos_of_pos_of_lt_pi_div_two
    (polarRadius_pos positive) (by linarith only [polarRadius_lt small, pi_gt_d2])
  let reindex := finCongr (south_rowSize_eq positive small)
  rw [regularSlopePolygon_eq_iUnion_fan polarFrame sides radius, Set.image_iUnion, Set.preimage_iUnion]
  rw [← reindex.surjective.iUnion_comp]
  apply congrArg Set.iUnion
  funext e
  change polarReflection ⁻¹' (gnomonicNormal '' convexHull ℝ
    {0, regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) e.val,
      regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) (e.val + 1)}) = _
  rw [← southChordBasis_chart_range positive small,
    gnomonicNormal_image_chordChart _ (southChordBasis_upward positive small e)]
  ext p
  change (‖polarReflection p‖ = 1 ∧ ∀ i,
    0 ≤ (southChordBasis positive small e).coord i (polarReflection p)) ↔ _
  rw [polarReflection.norm_map]
  have repr_eq : (southChordBasis positive small e).repr (polarReflection p) = (B (South e)).repr p := by
    rw [southChordBasis, Basis.map_repr, LinearEquiv.trans_apply]
    exact congrArg _ (polarReflection.toLinearEquiv.symm_apply_apply p)
  simp only [Basis.coord_apply, repr_eq, Set.mem_ofPred_eq]

end Unfoldings.FewestNets.AcuteLatitudeGrid
