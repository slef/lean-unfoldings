module

public import Unfoldings.Geometry.RegularPolygonFan
public import Unfoldings.Geometry.ComplexRotation
public import Unfoldings.Geometry.AffineMaximum

/-! Each active supporting line of a regular polygon cuts its exact ring side. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

variable (frame : Plane ≃ₗᵢ[ℝ] ℂ) {k : ℕ}

/-- The endpoints of a ring side can also be read modulo one complete turn. -/
theorem regularRingVertex_add_sideCount (sides : 3 ≤ k) (R : ℝ) (j : ℕ) :
    regularRingVertex frame k R (j + k) = regularRingVertex frame k R j := by
  have k_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have period : 2 * ((j + k : ℕ) : ℝ) * (π / (k : ℝ)) =
      2 * (j : ℝ) * (π / (k : ℝ)) + 2 * π := by
    push_cast
    field_simp [k_pos.ne']
  simp only [regularRingVertex, period]
  congr 2
  apply Complex.ext
  · simp only [polarRay_re, cos_add_two_pi]
  · simp only [polarRay_im, sin_add_two_pi]

/-- An active side consists exactly of the closed segment joining its two
consecutive vertices, including the side that closes the ring. -/
theorem regularSlopePolygon_activeSide_eq (sides : 3 ≤ k) {R : ℝ} (positive : 0 < R)
    (i : Fin k) :
    {p ∈ regularSlopePolygon frame k R | inner ℝ (regularSideNormal frame i) p = R * cos (π / k)} =
      segment ℝ (regularRingVertex frame k R i.val) (regularRingVertex frame k R (i.val + 1)) := by
  let x := π / (k : ℝ)
  let θ := (2 * (i.val : ℝ) + 1) * x
  let A := regularRingVertex frame k R i.val
  let B := regularRingVertex frame k R (i.val + 1)
  let L := (complexRotation (-θ)).comp frame.toLinearIsometry
  let h := R * cos x
  let w := R * sin x
  have k_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have x_pos : 0 < x := div_pos pi_pos k_pos
  have x_small : x ≤ π / 3 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by exact_mod_cast sides)
  have w_pos : 0 < w := mul_pos positive
    (sin_pos_of_pos_of_lt_pi x_pos (by linarith only [x_small, pi_pos]))
  have real (p : Plane) : (L p).re = inner ℝ (regularSideNormal frame i) p := by
    change (polarRay (-θ) * frame p).re = inner ℝ (frame.symm (polarRay θ)) p
    rw [← frame.symm_apply_apply p, frame.symm.inner_map_map,
      Complex.mul_re, Complex.inner, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, polarRay_re, polarRay_im, polarRay_re, polarRay_im,
      cos_neg, sin_neg]
    rw [frame.apply_symm_apply]
    ring
  have ring (j : ℕ) :
      L (regularRingVertex frame k R j) = (R : ℂ) * polarRay (2 * (j : ℝ) * x - θ) := by
    change polarRay (-θ) * frame (R • frame.symm (polarRay (2 * (j : ℝ) * x))) = _
    rw [map_smul, frame.apply_symm_apply, Complex.real_smul, ← mul_left_comm, ← polarRay_add]
    congr 2
    ring
  have at_A : L A = ⟨h, -w⟩ := by
    rw [show A = regularRingVertex frame k R i.val from rfl, ring,
      show 2 * (i.val : ℝ) * x - θ = -x by dsimp [θ]; ring]
    apply Complex.ext
    · simp only [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, polarRay_re,
        cos_neg, zero_mul, sub_zero]
    · simp only [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, polarRay_im,
        sin_neg, zero_mul, add_zero, mul_neg]
  have at_B : L B = ⟨h, w⟩ := by
    rw [show B = regularRingVertex frame k R (i.val + 1) from rfl, ring, Nat.cast_add, Nat.cast_one,
      show 2 * ((i.val : ℝ) + 1) * x - θ = x by dsimp [θ]; ring]
    apply Complex.ext
    · simp only [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, polarRay_re,
        zero_mul, sub_zero]
    · simp only [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, polarRay_im,
        zero_mul, add_zero]
  ext p
  constructor
  · rintro ⟨inside, active⟩
    have re : (L p).re = h := (real p).trans active
    have norm_le : ‖L p‖ ≤ R := (L.norm_map p).trans_le
      (norm_le_of_mem_regularSlopePolygon frame sides inside)
    have squared := pow_le_pow_left₀ (norm_nonneg _) norm_le 2
    have projection := Complex.sq_norm_sub_sq_re (L p)
    have width_sq : h ^ 2 + w ^ 2 = R ^ 2 := by
      dsimp only [h, w]
      linear_combination R ^ 2 * (cos_sq_add_sin_sq x)
    have im_bounded : |(L p).im| ≤ w := by
      apply (sq_le_sq₀ (abs_nonneg _) w_pos.le).mp
      rw [sq_abs]
      rw [re] at projection
      linarith only [squared, projection, width_sq]
    let t := ((L p).im + w) / (2 * w)
    have denom : 0 < 2 * w := by positivity
    have param : t ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (by linarith only [(abs_le.mp im_bounded).1]) denom.le,
        (div_le_one denom).mpr (by linarith only [(abs_le.mp im_bounded).2])⟩
    have height : t * (2 * w) = (L p).im + w := div_mul_cancel₀ _ denom.ne'
    rw [segment_eq_image_lineMap]
    refine ⟨t, param, L.injective ?_⟩
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, at_A, at_B]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re]
      rw [re]
      ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      linarith only [height]
  · intro on_side
    have inside : p ∈ regularSlopePolygon frame k R :=
      ((regularPolygonSideDirections frame sides positive).convex.segment_subset
        (regularRingVertex_mem frame sides positive.le i.isLt.le)
        (regularRingVertex_mem frame sides positive.le i.isLt)) on_side
    refine ⟨inside, ?_⟩
    obtain ⟨t, _, rfl⟩ := (segment_eq_image_lineMap ℝ A B).subset on_side
    rw [← real, AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, at_A, at_B]
    simp only [Complex.add_re, Complex.smul_re]
    change (1 - t) * h + t * h = h
    ring

/-- The actual planar frontier is the union of these sides, with no radial
edges from the fan triangulation. -/
theorem frontier_regularSlopePolygon (sides : 3 ≤ k) {R : ℝ} (positive : 0 < R) :
    frontier (regularSlopePolygon frame k R) = ⋃ i : Fin k,
      segment ℝ (regularRingVertex frame k R i.val) (regularRingVertex frame k R (i.val + 1)) := by
  let P := regularPolygonSideDirections frame sides positive
  ext p
  constructor
  · intro boundary
    obtain ⟨i, active⟩ := P.exists_active_side boundary
    have inside := P.isClosed.frontier_subset boundary
    exact Set.mem_iUnion.mpr ⟨i,
      (regularSlopePolygon_activeSide_eq frame sides positive i).subset ⟨inside, active⟩⟩
  · intro reaches
    obtain ⟨i, on_side⟩ := Set.mem_iUnion.mp reaches
    obtain ⟨inside, active⟩ :=
      (regularSlopePolygon_activeSide_eq frame sides positive i).symm.subset on_side
    refine ⟨subset_closure inside, fun h => ?_⟩
    let f := innerSL ℝ (P.normal i)
    have nonzero : f ≠ 0 := by
      intro zero
      have equal := DFunLike.congr_fun zero (P.normal i)
      change inner ℝ (P.normal i) (P.normal i) = 0 at equal
      have unit := P.unit i
      rw [inner_self_eq_zero.mp equal, norm_zero] at unit
      exact zero_ne_one unit
    have strict := supporting_functional_lt_on_interior f nonzero _
      (P.offset i) (fun z hz => P.side_bound hz i) p h
    exact strict.ne active

end Unfoldings
