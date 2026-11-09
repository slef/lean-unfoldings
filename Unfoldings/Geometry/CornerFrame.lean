module

public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.Angles
public import Mathlib.Analysis.Complex.Isometry

/-!
# Rigid normalized coordinates at an actual triangle corner

Place the apex at zero and its first edge on the positive real axis. Choose
the reflection so the other boundary ray lies in the upper half-plane.
Existence follows from an actual two-point rigid motion and noncollinearity.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Rigid complex coordinates fixing the apex, first boundary ray and side convention. -/
structure CornerFrame (T : Triangle) (i : Fin 3) where
  place : Plane ≃ᵃⁱ[ℝ] ℂ
  apex : place (T.vertex i) = 0
  first : place (T.vertex (next i)) = (dist (T.vertex i) (T.vertex (next i)) : ℂ)
  upper : 0 < (place (T.vertex (next (next i)))).im

theorem exists_cornerFrame (T : Triangle) (i : Fin 3) : Nonempty (T.CornerFrame i) := by
  let length := dist (T.vertex i) (T.vertex (next i))
  have length_pos : 0 < length := dist_pos.mpr (T.edge_endpoints_ne i)
  let target : Plane := Complex.orthonormalBasisOneI.repr (length : ℂ)
  have target_distance : dist (0 : Plane) target = length := by
    calc
      dist (0 : Plane) target = dist (0 : ℂ) (length : ℂ) := by
        simpa only [map_zero] using
          Complex.orthonormalBasisOneI.repr.isometry.dist_eq (0 : ℂ) (length : ℂ)
      _ = length := by
        rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos length_pos]
  let p := twoPointIsometry (T.vertex i) (T.vertex (next i)) 0 target
  have p_apex : p (T.vertex i) = 0 := twoPointIsometry_left _ _ _ _
  have p_first : p (T.vertex (next i)) = target :=
    twoPointIsometry_right _ _ _ _ target_distance.symm
  let frame : Plane ≃ᵃⁱ[ℝ] ℂ :=
    p.trans Complex.orthonormalBasisOneI.repr.symm.toAffineIsometryEquiv
  have frame_apex : frame (T.vertex i) = 0 := by
    change Complex.orthonormalBasisOneI.repr.symm (p (T.vertex i)) = 0
    rw [p_apex, map_zero]
  have frame_first : frame (T.vertex (next i)) = (length : ℂ) := by
    change Complex.orthonormalBasisOneI.repr.symm (p (T.vertex (next i))) = _
    rw [p_first]
    exact Complex.orthonormalBasisOneI.repr.symm_apply_apply _
  have area := orient_map_ne_zero p (T.orient_edge_ne_zero i)
  rw [p_apex, p_first] at area
  have target_coordinates : target 0 = length ∧ target 1 = 0 := by
    constructor <;> simp [target, Complex.orthonormalBasisOneI_repr_apply]
  have second_coordinate : (p (T.vertex (next (next i)))) 1 ≠ 0 := by
    intro zero
    apply area
    change orient (0 : Plane) target (p (T.vertex (next (next i)))) = 0
    simp [orient, target_coordinates.1, target_coordinates.2, zero]
  have imaginary : (frame (T.vertex (next (next i)))).im ≠ 0 := by
    change (Complex.orthonormalBasisOneI.repr.symm
      (p (T.vertex (next (next i))))).im ≠ 0
    simpa only [Complex.orthonormalBasisOneI_repr_symm_apply,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] using second_coordinate
  by_cases upper : 0 < (frame (T.vertex (next (next i)))).im
  · exact ⟨⟨frame, frame_apex, frame_first, upper⟩⟩
  · let reflected := frame.trans Complex.conjLIE.toAffineIsometryEquiv
    refine ⟨⟨reflected, ?_, ?_, ?_⟩⟩
    · change starRingEnd ℂ (frame (T.vertex i)) = 0
      rw [frame_apex]
      exact map_zero _
    · change starRingEnd ℂ (frame (T.vertex (next i))) = (length : ℂ)
      rw [frame_first]
      exact Complex.conj_ofReal _
    · change 0 < (starRingEnd ℂ (frame (T.vertex (next (next i))))).im
      rw [Complex.conj_im]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt upper) imaginary)

/-- Choose a normalized frame only after the rigid construction has been proved. -/
def cornerFrame (T : Triangle) (i : Fin 3) : T.CornerFrame i :=
  Classical.choice (T.exists_cornerFrame i)

end Unfoldings.Triangle
