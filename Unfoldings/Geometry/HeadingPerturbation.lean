module

public import Unfoldings.Geometry.HeadingChordError
public import Unfoldings.Geometry.ChordPerturbation
public import Unfoldings.Geometry.ComplexRotation

/-! The paper's radial-margin and length-constant estimates under real heading perturbations. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P Q : PolygonalChain ℂ n) (error : Fin n → ℝ)
  (rotated : ∀ i, Q.edge i = polarRay (error i) * P.edge i)

include rotated in
theorem heading_relative_chord_error {anchor ε D : ℝ} (nonnegative : 0 ≤ ε)
    (bound : ∀ i, |error i - anchor| ≤ ε)
    (length_bound : P.projectedLength ≤ D * ‖P.vertex (Fin.last n) - P.vertex 0‖) :
    ‖polarRay (-anchor) * (Q.vertex (Fin.last n) - Q.vertex 0) -
      (P.vertex (Fin.last n) - P.vertex 0)‖ ≤
        (D * ε) * ‖P.vertex (Fin.last n) - P.vertex 0‖ := by
  calc
    _ ≤ ε * P.projectedLength := P.heading_chord_error Q error rotated bound
    _ ≤ ε * (D * ‖P.vertex (Fin.last n) - P.vertex 0‖) :=
      mul_le_mul_of_nonneg_left length_bound nonnegative
    _ = _ := by ring

include rotated in
/-- Aligning the final tangent gives exactly `(d - D ε) / (1 + D ε)` as the new margin. -/
theorem heading_radial_margin {anchor ε D d : ℝ} (epsilon : 0 ≤ ε) (constant : 0 ≤ D)
    (bound : ∀ i, |error i - anchor| ≤ ε) (small : D * ε < d)
    (length_bound : P.projectedLength ≤ D * ‖P.vertex (Fin.last n) - P.vertex 0‖)
    (v : ℂ) (margin : d * (‖P.vertex (Fin.last n) - P.vertex 0‖ * ‖v‖) ≤
      inner ℝ (P.vertex (Fin.last n) - P.vertex 0) v) :
    ((d - D * ε) / (1 + D * ε)) *
      (‖Q.vertex (Fin.last n) - Q.vertex 0‖ * ‖polarRay anchor * v‖) ≤
        inner ℝ (Q.vertex (Fin.last n) - Q.vertex 0) (polarRay anchor * v) := by
  have chord_error := P.heading_relative_chord_error Q error rotated epsilon bound length_bound
  have estimate := radial_margin_of_chord_error (mul_nonneg constant epsilon) small
    chord_error margin
  have inner_equal := (complexRotation (-anchor)).inner_map_map
    (Q.vertex (Fin.last n) - Q.vertex 0) (complexRotation anchor v)
  rw [complexRotation_neg_cancel] at inner_equal
  simp only [complexRotation_apply] at inner_equal
  rw [inner_equal] at estimate
  simpa only [norm_mul, norm_polarRay, one_mul] using estimate

include rotated in
/-- Rotations preserve link lengths, and chord control gives the new length constant. -/
theorem heading_length_bound {anchor ε D : ℝ} (epsilon : 0 ≤ ε) (constant : 0 ≤ D)
    (bound : ∀ i, |error i - anchor| ≤ ε) (small : D * ε < 1)
    (length_bound : P.projectedLength ≤ D * ‖P.vertex (Fin.last n) - P.vertex 0‖) :
    Q.projectedLength ≤ (D / (1 - D * ε)) * ‖Q.vertex (Fin.last n) - Q.vertex 0‖ := by
  have chord_error := P.heading_relative_chord_error Q error rotated epsilon bound length_bound
  have estimate := length_constant_of_chord_error constant small chord_error length_bound
  rw [P.projectedLength_eq_of_rotated_edges Q error rotated]
  simpa only [norm_mul, norm_polarRay, one_mul] using estimate

end Unfoldings.PolygonalChain
