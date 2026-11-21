module

public import Unfoldings.Cap.SharpSectionHinge
public import Unfoldings.Cap.IntrinsicSectionTurns

/-! The sharp intrinsic turn budget for a generic straight cap section. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- The actual single-seam development incurs the sharp local turn budget. -/
theorem intrinsicSectionTurn_le_sin_mul_spatial (K : ConvexCap C) {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (s : C.Seam) (d : Plane) (transverse : orient 0 (K.projectedSeamVector s) d ≠ 0) :
    K.intrinsicSectionTurn s d ≤
      sin phi * angle (K.spatialDirection (C.left s).face d)
        (K.spatialDirection (C.right s).face d) := by
  unfold intrinsicSectionTurn
  rw [(C.singleSeamDevelopment s (K.folding.incident_faces_ne s)).retained_section_angle_eq_abs_sub
    K s (Set.mem_singleton s) d transverse]
  exact K.abs_spatialDirection_seam_angle_sub_le_sin_tilt_of_transverse nonnegative small tilt
    s d transverse

namespace SectionFaceTrace

variable {K : ConvexCap C} {p q : Plane} (T : K.SectionFaceTrace p q)
  (different : p ≠ q)
  (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)

/-- A true transverse section turn costs the spatial bend times the sine of
the tilt, and a repeated original-face label incurs no turn. -/
theorem intrinsicTurn_le_sin_mul_spatial {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi)
    (i : Fin T.turns) :
    T.intrinsicTurn different regular i ≤
      sin phi * angle (K.spatialDirection (T.face i.castSucc) (q - p))
        (K.spatialDirection (T.face i.succ) (q - p)) := by
  classical
  unfold intrinsicTurn
  split
  · rename_i changes
    let seam := T.exists_transverse_adjacent_seam different regular i changes
    have faces := seam.choose_spec.1
    have bound := K.intrinsicSectionTurn_le_sin_mul_spatial
      nonnegative small tilt seam.choose (q - p) seam.choose_spec.2.2
    rcases faces with faces | faces
    · rwa [faces.1, faces.2] at bound
    · rwa [faces.1, faces.2, angle_comm] at bound
  · exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith [pi_pos]))
      (angle_nonneg _ _)

/-- All intrinsic hinge turns along a generic straight section total at
most twice the tilt times its sine. -/
theorem sum_intrinsicTurn_le_sin_tilt {phi : ℝ}
    (nonnegative : 0 ≤ phi) (small : phi < π / 2) (tilt : K.TiltBound phi) :
    (∑ i, T.intrinsicTurn different regular i) ≤ 2 * phi * sin phi := by
  have sum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T.turns))) (fun i _ =>
    T.intrinsicTurn_le_sin_mul_spatial different regular nonnegative small tilt i)
  rw [← Finset.mul_sum] at sum
  have sine : 0 ≤ sin phi := sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith [pi_pos])
  have bound := mul_le_mul_of_nonneg_left
    (T.sum_spatialDirection_turn_le_tilt different nonnegative small tilt) sine
  exact sum.trans (bound.trans_eq (mul_comm _ _))

end SectionFaceTrace
end Unfoldings.ConvexCap
