module

public import Unfoldings.Cap.SharpSectionFans

/-! The sharp sine factor for an actual straight fan split into two supporting planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Subdivision creates more link corners but leaves the true turn at one
transverse crease equal to the two endpoint-angle expression. -/
theorem abs_two_flat_link_turn_le_sin_tilt {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ)
    (s : C.Seam) (d : Plane) (transverse : orient 0 (K.projectedSeamVector s) d ≠ 0)
    {w : C.Vertex Set.univ} {n m : ℕ}
    (left : (C.linkSystem Set.univ w).Chain n) (right : (C.linkSystem Set.univ w).Chain m)
    (left_slope : ∀ i, K.normalSlope (left.point i).val.1.1 = K.normalSlope (C.left s).face)
    (right_slope : ∀ i, K.normalSlope (right.point i).val.1.1 = K.normalSlope (C.right s).face)
    (left_short : (∑ i : Fin (n + 1),
      (K.projectedTriangle (left.point i).val.1.1).cornerAngle (left.point i).val.1.2) ≤ π)
    (right_short : (∑ i : Fin (m + 1),
      (K.projectedTriangle (right.point i).val.1.1).cornerAngle (right.point i).val.1.2) ≤ π)
    {a b t : ℝ} (a_pos : 0 < a) (b_pos : 0 < b) (t_ne : t ≠ 0)
    (first : K.projectedIntervalRay left 0 = a • d)
    (seam_left : K.projectedIntervalRay left (Fin.last (n + 1)) = t • K.projectedSeamVector s)
    (seam_right : K.projectedIntervalRay right 0 = t • K.projectedSeamVector s)
    (last : K.projectedIntervalRay right (Fin.last (m + 1)) = b • (-d)) :
    |π - ((∑ i : Fin (n + 1), (C.triangle (left.point i).val.1.1).cornerAngle
        (left.point i).val.1.2) +
      ∑ i : Fin (m + 1), (C.triangle (right.point i).val.1.1).cornerAngle
        (right.point i).val.1.2)| ≤
      sin φ * angle (K.spatialDirection (C.left s).face d)
        (K.spatialDirection (C.right s).face d) := by
  have left_sum := K.sum_flat_link_corner_angles left (C.left s).face left_slope
    (K.projectedInterval_halfplane_of_sum_le_pi left left_short)
  have right_sum := K.sum_flat_link_corner_angles right (C.right s).face right_slope
    (K.projectedInterval_halfplane_of_sum_le_pi right right_short)
  have scale (f : Face) (c : ℝ) (x : Plane) :
      K.spatialDirection f (c • x) = c • K.spatialDirection f x := by
    simp only [spatialDirection, pullbackDirection, map_smul]
  have neg (f : Face) (x : Plane) : K.spatialDirection f (-x) = -K.spatialDirection f x := by
    simp only [spatialDirection, pullbackDirection, map_neg]
  rw [left_sum, right_sum, first, last, seam_left, seam_right, scale, scale, scale, scale,
    neg, ← K.spatialDirection_seam s, angle_smul_left_of_pos _ _ a_pos,
    angle_smul_right_of_pos _ _ b_pos]
  have estimate := K.abs_two_plane_fan_turn_le_sin_tilt nonnegative small tilt s d transverse
  rcases lt_or_gt_of_ne t_ne with negative | positive
  · rw [angle_smul_right_of_neg _ _ negative, angle_smul_left_of_neg _ _ negative]
    exact estimate.2
  · rw [angle_smul_right_of_pos _ _ positive, angle_smul_left_of_pos _ _ positive]
    exact estimate.1

end Unfoldings.ConvexCap
