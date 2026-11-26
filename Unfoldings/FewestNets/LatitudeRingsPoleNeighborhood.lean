module

public import Unfoldings.FewestNets.LatitudeRingsOrientation
public import Unfoldings.Geometry.RadialTrianglePartition

/-! There is a neighborhood of the north pole containing only northern fan directions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.LatitudeRings

open Real Module
open scoped Topology

variable {G : LatitudeRings}

local notation "North" => latitudeSite 0 0
local notation "South" => latitudeSite π 0

/-- The horizontal signed projection onto the meridian of longitude `t`. -/
def meridianCoordinate (t : ℝ) : Space →ₗ[ℝ] ℝ :=
  cos t • (PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) 0) +
    sin t • (PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) 1)

theorem meridianCoordinate_latitudeSite (t row lon : ℝ) :
    meridianCoordinate t (latitudeSite row lon) = sin row * cos (lon - t) := by
  rw [cos_sub]
  simp only [meridianCoordinate, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    PiLp.projₗ_apply, latitudeSite]
  change cos t * (sin row * cos lon) + sin t * (sin row * sin lon) = _
  ring

private theorem meridianCoordinate_rowSite_pos (hG : Admissible G)
    {row k : ℕ} (valid : row ≤ stripCount G) {t : ℝ}
    (close : |rowLongitude (rowSize G row) k - t| ≤ π / (rowSize G row : ℝ)) :
    0 < meridianCoordinate t (rowSite G row k) := by
  have gap := (longitudeStep_pos_lt_pi hG valid).2
  have half : π / (rowSize G row : ℝ) < π / 2 := by
    unfold longitudeStep at gap
    linarith only [gap, show (2 * π) / (rowSize G row : ℝ) =
      2 * (π / (rowSize G row : ℝ)) by ring]
  have near := abs_lt.mp (close.trans_lt half)
  have row_loc := colatitude_mem hG valid
  exact (meridianCoordinate_latitudeSite _ _ _).symm ▸
    mul_pos (sin_pos_of_pos_of_lt_pi row_loc.1 row_loc.2) (cos_pos_of_mem_Ioo near)

/-- The horizontal projections of the three sites of a sweep triangle are strictly
positive along its base midpoint meridian. -/
theorem annularVertices_common_meridian (hG : Admissible G)
    (i : AnnularTriangle G) : ∃ t : ℝ, ∀ k, 0 < meridianCoordinate t (annularVertices G i k) := by
  obtain ⟨j, i⟩ := i
  let step := sweepOrder (rowSize G j.val) (rowSize G (j.val + 1))
  have sorted := sweepOrder_sorted (rowSize G j.val) (rowSize G (j.val + 1))
  have lower : j.val ≤ stripCount G := j.isLt.le
  have upper : j.val + 1 ≤ stripCount G := Nat.succ_le_of_lt j.isLt
  unfold annularVertices
  change ∃ t : ℝ, ∀ k, 0 < meridianCoordinate t (latitudeSweepChordVertices G j.val step i k)
  unfold latitudeSweepChordVertices
  rcases advance : step i with b | b
  · refine ⟨rowMidpoint _ b, fun k => ?_⟩
    have near := upperSweep_near_lower_midpoint step sorted
      (rowSize_pos hG upper) i b advance
    have left := meridianCoordinate_rowSite_pos hG lower
      (by rw [abs_sub_comm]; exact rowMidpoint_closest_left b)
    have right := meridianCoordinate_rowSite_pos hG lower (k := b.val + 1)
      (by rw [rowLongitude_succ_sub_rowMidpoint, abs_of_nonneg (by positivity)])
    have apex := meridianCoordinate_rowSite_pos hG upper (by rwa [abs_sub_comm])
    fin_cases k
    · exact left
    · exact right
    · exact apex
  · refine ⟨rowMidpoint _ b, fun k => ?_⟩
    have near := lowerSweep_near_upper_midpoint step sorted
      (rowSize_pos hG lower) i b advance
    have left := meridianCoordinate_rowSite_pos hG upper
      (by rw [abs_sub_comm]; exact rowMidpoint_closest_left b)
    have right := meridianCoordinate_rowSite_pos hG upper (k := b.val + 1)
      (by rw [rowLongitude_succ_sub_rowMidpoint, abs_of_nonneg (by positivity)])
    have apex := meridianCoordinate_rowSite_pos hG lower (by rwa [abs_sub_comm])
    fin_cases k
    · exact right
    · exact left
    · exact apex

private theorem not_all_nonneg_of_linear_separator (b : Basis (Fin 3) ℝ Space)
    (ℓ : Space →ₗ[ℝ] ℝ) {p : Space} (nonzero : p ≠ 0) (p_side : ℓ p ≤ 0)
    (vertex_side : ∀ k, 0 < ℓ (b k)) : ¬ ∀ k, 0 ≤ b.coord k p := by
  intro nonneg
  have exists_pos : ∃ k, 0 < b.coord k p := by
    by_contra! all
    have zero (k : Fin 3) : b.coord k p = 0 := le_antisymm (all k) (nonneg k)
    apply nonzero
    have expand := b.sum_repr p
    change (∑ k, b.coord k p • b k) = p at expand
    simpa only [zero, zero_smul, Finset.sum_const_zero] using expand.symm
  obtain ⟨j, h_j⟩ := exists_pos
  apply p_side.not_gt
  have expand := congrArg ℓ (b.sum_repr p)
  change ℓ (∑ k, b.coord k p • b k) = ℓ p at expand
  rw [map_sum] at expand
  simp only [map_smul, smul_eq_mul] at expand
  rw [← expand]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (nonneg k) (vertex_side k).le)
    ⟨j, Finset.mem_univ _, mul_pos h_j (vertex_side j)⟩

private theorem northPole_nonzero : North ≠ 0 := by
  intro impossible
  have norm := latitudeSite_unit 0 0
  rw [impossible, norm_zero] at norm
  exact zero_ne_one norm

/-- The north pole is outside every closed annular chord-triangle cone. -/
theorem northPole_outside_annular (hG : Admissible G)
    (i : AnnularTriangle G) (b : Basis (Fin 3) ℝ Space)
    (basis : ∀ k, b k = annularVertices G i k) :
    ¬ ∀ k, 0 ≤ b.coord k North := by
  obtain ⟨t, positive_side⟩ := annularVertices_common_meridian hG i
  exact not_all_nonneg_of_linear_separator b (meridianCoordinate t) northPole_nonzero
    (by rw [meridianCoordinate_latitudeSite, sin_zero, zero_mul])
    (fun k => (basis k).symm ▸ positive_side k)

/-- The north pole is outside every closed southern chord-triangle cone. -/
theorem northPole_outside_south (hG : Admissible G)
    (e : Fin (rowSize G (stripCount G))) (b : Basis (Fin 3) ℝ Space)
    (basis : ∀ k, b k = chordVertices G (.inr (.inr e)) k) :
    ¬ ∀ k, 0 ≤ b.coord k North := by
  let ℓ : Space →ₗ[ℝ] ℝ := -PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) 2
  apply not_all_nonneg_of_linear_separator b ℓ northPole_nonzero
  · change -(cos 0) ≤ 0
    simp
  · have south (k : ℕ) : 0 < ℓ (rowSite G (stripCount G) k) := by
      change 0 < -cos (colatitude G (stripCount G))
      exact neg_pos.mpr hG.southern
    intro k
    rw [basis]
    fin_cases k
    · change 0 < -cos π
      simp
    · exact south _
    · exact south _

/-- All nonnorthern triangles remain absent on an open neighborhood of the pole. -/
theorem eventually_northPole_outside_elsewhere (hG : Admissible G)
    (b : ChordFace G → Basis (Fin 3) ℝ Space)
    (basis : ∀ i k, b i k = chordVertices G i k) :
    ∀ᶠ p in 𝓝 North, ∀ i : AnnularTriangle G ⊕ Fin (rowSize G (stripCount G)),
      ¬ ∀ k, 0 ≤ (b (.inr i)).coord k p := by
  apply Filter.eventually_all.mpr
  intro i
  have absent : ¬ ∀ k, 0 ≤ (b (.inr i)).coord k North := by
    rcases i with e | e
    · exact northPole_outside_annular hG e _ (basis _)
    · exact northPole_outside_south hG e _ (basis _)
  push Not at absent
  obtain ⟨k, negative⟩ := absent
  have near : ∀ᶠ p in 𝓝 North, (b (.inr i)).coord k p < 0 :=
    (isOpen_lt ((b (.inr i)).coord k).continuous_of_finiteDimensional
      continuous_const).mem_nhds negative
  exact near.mono (fun _ h all => h.not_ge (all k))

end Unfoldings.FewestNets.LatitudeRings
