module

public import Unfoldings.Geometry.BallRigidity
public import Unfoldings.Geometry.AffineEnd

/-!
# Rigid extension of isometries on convex sets with interior

A whole interior ball constructs the rigid map. Segment preservation then
extends its agreement to the entire convex set, including its boundary.
This will let local face patches determine actual whole-face placements.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]

theorem exists_affineIsometry_extension_convex {s : Set E} (convex : Convex ℝ s)
    (interior_nonempty : (interior s).Nonempty) (f : s → F) (isometry : Isometry f) :
    ∃ A : E →ᵃⁱ[ℝ] F, ∀ x : s, A x.val = f x := by
  obtain ⟨c, inside⟩ := interior_nonempty
  obtain ⟨r, positive, interior_ball⟩ := Metric.isOpen_iff.mp isOpen_interior c inside
  have ball_inside := interior_ball.trans interior_subset
  let include_ball (x : Metric.ball c r) : s := ⟨x.val, ball_inside x.property⟩
  have include_isometry : Isometry include_ball := fun _ _ => rfl
  let B : IsometricBallMap E F :=
    ⟨c, r, positive, f ∘ include_ball, isometry.comp include_isometry⟩
  let center : s := ⟨c, interior_subset inside⟩
  have at_center : B.affineExtension c = f center :=
    B.affineExtension_agrees ⟨c, Metric.mem_ball_self positive⟩
  refine ⟨B.affineExtension, ?_⟩
  intro x
  let t := min (B.scale x.val) 1
  have positive_t : 0 < t := lt_min (B.scale_pos x.val) zero_lt_one
  have before : t ≤ 1 := min_le_right _ _
  have near : AffineMap.lineMap c x.val t ∈ Metric.ball c r := by
    have big_near := B.scale_near x.val
    change dist (AffineMap.lineMap c x.val (B.scale x.val)) c < r at big_near
    change dist (AffineMap.lineMap c x.val t) c < r
    rw [dist_comm, dist_left_lineMap, Real.norm_of_nonneg positive_t.le]
    rw [dist_comm, dist_left_lineMap, Real.norm_of_nonneg (B.scale_pos x.val).le] at big_near
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) dist_nonneg).trans_lt big_near
  have at_sample : B.affineExtension (AffineMap.lineMap c x.val t) =
      f ⟨AffineMap.lineMap c x.val t, ball_inside near⟩ := B.affineExtension_agrees ⟨_, near⟩
  have straight := isometry_lineMap_on_convex convex f isometry center x t ⟨positive_t.le, before⟩
  have equal : AffineMap.lineMap (f center) (B.affineExtension x.val) t =
      AffineMap.lineMap (f center) (f x) t := by
    calc
      _ = AffineMap.lineMap (B.affineExtension c) (B.affineExtension x.val) t := by
        rw [at_center]
      _ = B.affineExtension (AffineMap.lineMap c x.val t) :=
        (B.affineExtension.toAffineMap.apply_lineMap c x.val t).symm
      _ = _ := at_sample.trans straight
  simp only [AffineMap.lineMap_apply_module'] at equal
  exact sub_left_inj.mp (smul_right_injective F positive_t.ne' (add_right_cancel equal))

theorem exists_rigid_extension_convex {s : Set E} [FiniteDimensional ℝ E]
    [StrictConvexSpace ℝ E] (convex : Convex ℝ s) (interior_nonempty : (interior s).Nonempty)
    (f : s → E) (isometry : Isometry f) : ∃ A : E ≃ᵃⁱ[ℝ] E, ∀ x : s, A x.val = f x := by
  obtain ⟨A, agrees⟩ := exists_affineIsometry_extension_convex convex interior_nonempty f isometry
  let rigid : E ≃ᵃⁱ[ℝ] E :=
    { AffineEquiv.ofBijective (φ := A.toAffineMap)
        ⟨A.injective, affineIsometryEnd_surjective A⟩ with norm_map := A.norm_map }
  exact ⟨rigid, agrees⟩

end Unfoldings
