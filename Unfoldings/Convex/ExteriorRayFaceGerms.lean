module

public import Unfoldings.Convex.ExteriorBankSupports
public import Unfoldings.Geometry.AffineEnvelopeActiveGerm

/-! Two fixed one-sided planes describe the roof near every positive exterior ray point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.ExteriorPlan

variable {E : SlopeEnvelope} {V : Type*} (R : E.ExteriorPlan V) (M : E.FiniteSlopeModel)
  {A : Type} [Finite A] (P : SpatialEnvelope.WholePartition M.plane A)

omit [Finite A] in
/-- A terminal cell's actual support describes the entire one-sided roof germ at every
positive time. Inactive planes are removed by a derived finite strict-gap neighborhood. -/
theorem terminal_cell_ray_germ (v : V) (a : A) (T : ℝ)
    (tail : ∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint a) (side : Bool)
    (aligned : ∀ x ∈ P.footprint a,
      0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side x)
    {t : ℝ} (positive : 0 < t) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z (R.ray v t) < r →
      0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side z →
        SpatialEnvelope.height M.plane z = (M.plane (P.support a)).height z := by
  apply AffineEnvelope.exists_radius_height_eq_on_region (fun i => (M.plane i).height)
    (P.support a) (R.ray v t) (R.terminal_cell_support_active M P v a T tail t positive.le)
    {z | 0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) side z}
  intro j active_j z on_side
  have at_one := (R.plane_active_ray_iff M v j zero_lt_one).mpr
    ((R.plane_active_ray_iff M v j positive).mp active_j)
  exact R.terminal_cell_support_le_on_side M P v a T tail side aligned j at_one on_side

/-- Construct fixed actual left and right support cells for the entire positive ray.
At each positive point the roof is exactly their two affine height pieces on a whole ball.
No selected faces, fan angles, or local-model certificates are supplied. -/
theorem exists_whole_ray_two_face_germs (v : V) (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a →
      0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) (signs a) x) :
    ∃ a b : A, signs a = true ∧ signs b = false ∧ ∃ T : ℝ, 0 < T ∧
      (∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint a ∧ R.ray v t ∈ P.footprint b) ∧
      (∀ t : ℝ, 0 ≤ t →
        SpatialEnvelope.height M.plane (R.ray v t) = (M.plane (P.support a)).height (R.ray v t) ∧
        SpatialEnvelope.height M.plane (R.ray v t) = (M.plane (P.support b)).height (R.ray v t)) ∧
      ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ ∀ z, dist z (R.ray v t) < r →
        (0 ≤ orient (R.point v) (R.ray v 1) z →
          SpatialEnvelope.height M.plane z = (M.plane (P.support a)).height z) ∧
        (orient (R.point v) (R.ray v 1) z ≤ 0 →
          SpatialEnvelope.height M.plane z = (M.plane (P.support b)).height z) := by
  obtain ⟨a, b, ha, hb, T, positive, tail⟩ := P.exists_opposite_ray_cells
    (orientMap (R.point v) (R.ray v 1)) (orientMap_ne_zero (R.ray_endpoints_ne v))
    signs aligned (R.point v) (R.direction (R.slope v)) (fun t => by
      change orientMap (R.point v) (R.ray v 1) (R.ray v t) = 0
      rw [← R.ray_lineMap v t, orientMap_apply, orient_lineMap])
  have left : ∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint a := fun t ht => (tail t ht).1
  have right : ∀ t : ℝ, T ≤ t → R.ray v t ∈ P.footprint b := fun t ht => (tail t ht).2
  have aligned_a : ∀ x ∈ P.footprint a,
      0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) true x := by
    intro x member
    simpa only [ha] using aligned a x member
  have aligned_b : ∀ x ∈ P.footprint b,
      0 ≤ AffineArrangement.signed (orientMap (R.point v) (R.ray v 1)) false x := by
    intro x member
    simpa only [hb] using aligned b x member
  refine ⟨a, b, ha, hb, T, positive, tail, ?_, ?_⟩
  · intro t ht
    exact ⟨R.terminal_cell_support_active M P v a T left t ht,
      R.terminal_cell_support_active M P v b T right t ht⟩
  · intro t ht
    obtain ⟨r, rpos, first⟩ := R.terminal_cell_ray_germ M P v a T left true aligned_a ht
    obtain ⟨s, spos, last⟩ := R.terminal_cell_ray_germ M P v b T right false aligned_b ht
    refine ⟨min r s, lt_min rpos spos, ?_⟩
    intro z close
    constructor
    · intro on_side
      apply first z (close.trans_le (min_le_left r s))
      simpa only [AffineArrangement.signed_apply, ↓reduceIte, orientMap_apply] using on_side
    · intro on_side
      apply last z (close.trans_le (min_le_right r s))
      simpa only [AffineArrangement.signed_apply, Bool.false_eq_true, ↓reduceIte,
        orientMap_apply, neg_nonneg] using on_side

end Unfoldings.SlopeEnvelope.ExteriorPlan
