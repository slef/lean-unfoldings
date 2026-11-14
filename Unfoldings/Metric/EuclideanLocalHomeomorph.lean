module

public import Unfoldings.Metric.EuclideanAtlas
public import Mathlib.Topology.IsLocalHomeomorph

/-! A local metric isometry from a Euclidean surface to the plane is a local homeomorphism. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

/-- A planar isometry whose domain is a whole Euclidean ball has open image. -/
theorem isOpenEmbedding_of_isometric_ball_chart {T : Type*} [MetricSpace T]
    (center : Plane) (radius : ℝ) (positive : 0 < radius)
    (chart : T ≃ᵢ Metric.ball center radius) (g : T → Plane) (isometry : Isometry g) :
    IsOpenEmbedding g := by
  let B : IsometricBallMap Plane Plane := {
    center := center
    radius := radius
    positive := positive
    map := g ∘ chart.symm
    isometry := isometry.comp chart.symm.isometry }
  let motion : Plane ≃ᵢ Plane :=
    ⟨Equiv.ofBijective B.affineExtension
      ⟨B.affineExtension.injective, affineIsometryEnd_surjective B.affineExtension⟩,
      B.affineExtension.isometry⟩
  have agrees (y : T) : motion (chart y).val = g y := by
    have equal := B.affineExtension_agrees (chart y)
    change motion (chart y).val = g (chart.symm (chart y)) at equal
    simpa only [chart.symm_apply_apply] using equal
  have embedded : IsOpenEmbedding (fun y : T => motion (chart y).val) :=
    motion.toHomeomorph.isOpenEmbedding.comp
      (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp chart.toHomeomorph.isOpenEmbedding)
  exact (funext agrees) ▸ embedded

end Unfoldings

namespace Unfoldings.EuclideanAtlas

variable {X : Type*} [MetricSpace X] (A : EuclideanAtlas X) (f : X → Plane)

include A in
theorem isLocalHomeomorph_of_local_isometry
    (local_isometry : ∀ x, ∃ r > 0, Isometry (fun y : Metric.ball x r => f y.val)) :
    IsLocalHomeomorph f := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨a, apos, inside_chart, covers_chart⟩ := exists_open_chart_ball_radius (A x).chart
    (A x).open_domain (A x).open_image ⟨x, (A x).center_mem⟩
  obtain ⟨b, bpos, local_bound⟩ := local_isometry x
  let r := min a b
  have positive : 0 < r := lt_min apos bpos
  have inside : Metric.ball x r ⊆ (A x).domain :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans inside_chart
  have covers : Metric.ball ((A x).chart ⟨x, (A x).center_mem⟩).val r ⊆ (A x).image :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans covers_chart
  let L : Metric.ball x r ≃ᵢ
      Metric.ball ((A x).chart ⟨x, (A x).center_mem⟩).val r :=
    restrictChartBall (A x).chart ⟨x, (A x).center_mem⟩ inside covers
  let inclusion : Metric.ball x r → Metric.ball x b := fun y =>
    ⟨y.val, (Metric.ball_subset_ball (min_le_right _ _)) y.property⟩
  have restricted : Isometry (fun y : Metric.ball x r => f y.val) := by
    apply Isometry.of_dist_eq
    intro y z
    exact local_bound.dist_eq (inclusion y) (inclusion z)
  have embedded : IsOpenEmbedding (fun y : Metric.ball x r => f y.val) :=
    isOpenEmbedding_of_isometric_ball_chart _ _ positive L _ restricted
  exact ⟨Metric.ball x r, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self positive), embedded⟩

end Unfoldings.EuclideanAtlas
