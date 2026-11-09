module

public import Unfoldings.Metric.OpenChart
public import Unfoldings.Geometry.BallRigidity
public import Unfoldings.Geometry.AffineEnd

/-!
# An actual local isometry has a rigid expression in any Euclidean chart

Restrict the given chart and the isometry neighborhood to one whole metric
ball. Ball rigidity constructs its affine extension, and finite dimension
makes this a rigid equivalence. No openness of the image map is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [StrictConvexSpace ℝ E] [FiniteDimensional ℝ E] {D S : Set X} {U : Set E}

theorem exists_rigid_map_in_chart (chart : D ≃ᵢ U) (open_D : IsOpen D) (open_U : IsOpen U)
    (f : X → E) (open_S : IsOpen S) (isometry : Isometry (fun y : S => f y.val))
    (x : X) (in_D : x ∈ D) (in_S : x ∈ S) :
    ∃ r > 0, ∃ inside_D : Metric.ball x r ⊆ D, ∃ _inside_S : Metric.ball x r ⊆ S,
      ∃ A : E ≃ᵃⁱ[ℝ] E, ∀ y : Metric.ball x r,
        A (chart ⟨y.val, inside_D y.property⟩).val = f y.val := by
  obtain ⟨a, positive_a, included, cover⟩ :=
    exists_open_chart_ball_radius chart open_D open_U ⟨x, in_D⟩
  obtain ⟨b, positive_b, in_S_ball⟩ := Metric.isOpen_iff.mp open_S x in_S
  let r := min a b
  have positive : 0 < r := lt_min positive_a positive_b
  have inside_D : Metric.ball x r ⊆ D := (Metric.ball_subset_ball (min_le_left _ _)).trans included
  have inside_S : Metric.ball x r ⊆ S :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans in_S_ball
  have inside_U : Metric.ball (chart ⟨x, in_D⟩).val r ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans cover
  let L := restrictChartBall chart ⟨x, in_D⟩ inside_D inside_U
  let g := fun z => f (L.symm z).val
  have isometry_g : Isometry g := by
    intro z w
    exact (isometry ⟨(L.symm z).val, inside_S (L.symm z).property⟩
      ⟨(L.symm w).val, inside_S (L.symm w).property⟩).trans (L.symm.isometry z w)
  let B : IsometricBallMap E E :=
    ⟨(chart ⟨x, in_D⟩).val, r, positive, g, isometry_g⟩
  let A : E ≃ᵃⁱ[ℝ] E :=
    { AffineEquiv.ofBijective (φ := B.affineExtension.toAffineMap)
        ⟨B.affineExtension.injective, affineIsometryEnd_surjective B.affineExtension⟩
      with norm_map := B.affineExtension.norm_map }
  refine ⟨r, positive, inside_D, inside_S, A, ?_⟩
  intro y
  have equal := B.affineExtension_agrees (L y)
  change B.affineExtension (L y).val = f (L.symm (L y)).val at equal
  rw [L.symm_apply_apply] at equal
  exact equal

end Unfoldings
