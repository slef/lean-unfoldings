module

public import Unfoldings.FewestNets.RoundSelectorScalars
public import Unfoldings.Convex.ProgressDiskCone
public import Unfoldings.Convex.PolygonSideDirections
public import Unfoldings.Roof.CompatibleAdaptiveRouting

/-! A centered regular selector routes on original edges using its round progress disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

/-- Equidistant sides and the circumradius bound certify the paper's adaptive
polar routing and its outgoing radial margin. -/
theorem exists_roundSelectorRouting_of_aperture {I : Type*} [Finite I] [Nonempty I]
    {slopes : Set Plane} (B : PolygonSideDirections I slopes)
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (boundary : (frontier slopes).Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    {a x radius : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (x_nonneg : 0 ≤ x) (x_upper : x ≤ π / 6)
    (aperture : 1 / (√2 * cos x) < cos (π / 4 - 0.49 * a))
    (exit_margin : 0.48 * a ≤ cos (π / 4 + x)) (radius_pos : 0 < radius)
    (side_distance : ∀ i, B.offset i = radius * cos x)
    (radius_bound : ∀ p ∈ slopes, ‖p‖ ≤ radius)
    (angles : ∀ f, K.normalSlope f ∈ slopes → ∀ i,
      (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 0.99 * a) :
    let progress := radius / √2
    Nonempty (K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary
      (Metric.closedBall (0 : Plane) progress) progress (sin (0.495 * a)) (0.48 * a)) := by
  let progress := radius / √2
  let L := Metric.closedBall (0 : Plane) progress
  let theta := π / 2 - 0.99 * a
  let direction (p : Plane) := B.normal (B.sideIndex p)
  have root_pos : 0 < √(2 : ℝ) := by positivity
  have progress_pos : 0 < progress := div_pos radius_pos root_pos
  have cos_pos : 0 < cos x := cos_pos_of_mem_Ioo
    ⟨by linarith only [x_nonneg, pi_pos], by linarith only [x_upper, pi_pos]⟩
  have room := aperture.trans_le (cos_le_one _)
  have cos_lower : 1 / √(2 : ℝ) ≤ cos x := by
    apply (div_le_iff₀ root_pos).mpr
    exact (by simpa only [one_mul, mul_comm] using
      (div_lt_iff₀ (mul_pos root_pos cos_pos)).mp room : 1 < cos x * √(2 : ℝ)).le
  have support_dist : progress ≤ radius * cos x := by
    change radius / √2 ≤ _
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left cos_lower radius_pos.le
  have within : L ⊆ slopes := by
    intro p mem
    apply B.carrier_eq.symm.subset
    intro i
    rw [side_distance]
    have dist : ‖p‖ ≤ progress := by
      simpa only [L, Metric.mem_closedBall, dist_zero_right] using mem
    simpa only [B.unit, one_mul] using (real_inner_le_norm (B.normal i) p).trans
      (by simpa only [B.unit, one_mul] using dist.trans support_dist)
  have at_side {p : Plane} (hp : p ∈ frontier slopes) :
      inner ℝ (direction p) p = radius * cos x :=
    (B.sideIndex_active hp).trans (side_distance _)
  have p_range {p : Plane} (hp : p ∈ frontier slopes) :
      radius * cos x ≤ ‖p‖ ∧ ‖p‖ ≤ radius := by
    have bound := real_inner_le_norm (direction p) p
    rw [at_side hp, B.unit, one_mul] at bound
    exact ⟨bound, radius_bound _ (compact.isClosed.frontier_subset hp)⟩
  have cos_four : cos (π / 4) = 1 / √(2 : ℝ) := by
    rw [cos_pi_div_four]
    apply (div_eq_div_iff (by norm_num) root_pos.ne').mpr
    exact (Real.mul_self_sqrt (by norm_num : 0 ≤ (2 : ℝ))).trans (one_mul _).symm
  have half_range {p : Plane} (hp : p ∈ frontier slopes) :
      π / 4 - 0.49 * a ≤ arccos (progress / ‖p‖) ∧ arccos (progress / ‖p‖) ≤ π / 4 := by
    obtain ⟨low, high⟩ := p_range hp
    have p_pos := (mul_pos radius_pos cos_pos).trans_le low
    have upper : progress / ‖p‖ ≤ cos (π / 4 - 0.49 * a) := by
      calc
        _ ≤ progress / (radius * cos x) :=
          div_le_div_of_nonneg_left progress_pos.le (mul_pos radius_pos cos_pos) low
        _ = 1 / (√2 * cos x) := by
          dsimp only [progress]
          field_simp [radius_pos.ne', root_pos.ne', cos_pos.ne'] <;> ring
        _ ≤ _ := aperture.le
    have lower : cos (π / 4) ≤ progress / ‖p‖ := by
      rw [cos_four]
      calc
        _ = progress / radius := by
          dsimp only [progress]
          field_simp [radius_pos.ne', root_pos.ne'] <;> ring
        _ ≤ _ := div_le_div_of_nonneg_left progress_pos.le p_pos high
    have first := arccos_le_arccos upper
    have last := arccos_le_arccos lower
    rw [arccos_cos (by linarith only [small, pi_pos]) (by linarith only [positive, pi_pos])]
      at first
    rw [arccos_cos (by positivity) (by linarith only [pi_pos])] at last
    exact ⟨first, last⟩
  have theta_nonneg : 0 ≤ theta := by
    dsimp only [theta]
    linarith only [small, pi_pos]
  have theta_acute : (π / 2 + theta) / 2 < π / 2 := by
    dsimp only [theta]
    linarith only [positive]
  have interior_margin : cos ((π / 2 + theta) / 2) = sin (0.495 * a) := by
    rw [show (π / 2 + theta) / 2 = π / 2 - 0.495 * a by dsimp only [theta]; ring,
      cos_pi_div_two_sub]
  rw [← interior_margin]
  refine K.exists_compatibleAdaptiveRouting B.convex compact nonempty boundary no_boundary L
    within progress_pos Set.Subset.rfl theta_nonneg theta_acute angles ?_ direction ?_ ?_
  · intro p hp
    have bound := p_range hp
    have pr := support_dist.trans bound.1
    have genuine : p ≠ 0 := norm_pos_iff.mp (progress_pos.trans_le pr)
    let half := arccos (progress / ‖p‖)
    have ends := half_range hp
    refine ⟨p, 2 * half, genuine, ?_, ?_, ?_⟩
    · dsimp only [theta, half]
      linarith only [ends.1, positive]
    · dsimp only [half]
      linarith only [ends.2]
    · intro z nonzero
      rw [show 2 * half / 2 = half by ring]
      exact SlopeEnvelope.mem_historyCone_closedBall_iff_angle progress_pos.le genuine nonzero pr
  · intro p hp
    refine ⟨B.unit _, ?_, ?_⟩
    · rw [at_side hp]
      positivity
    · intro w hw
      rw [at_side hp, ← side_distance (B.sideIndex p)]
      exact B.side_bound hw _
  · intro p hp z hz
    by_cases zero : z = 0
    · simp [zero]
    have pr := support_dist.trans (p_range hp).1
    have pn : p ≠ 0 := norm_pos_iff.mp (progress_pos.trans_le pr)
    have zn : direction p ≠ 0 := by
      apply norm_pos_iff.mp
      change 0 < ‖B.normal (B.sideIndex p)‖
      rw [B.unit]
      norm_num
    have unit : ‖direction p‖ = 1 := B.unit _
    have limit : angle p z ≤ π / 4 :=
      ((SlopeEnvelope.mem_historyCone_closedBall_iff_angle progress_pos.le pn zero pr).mp hz)
        |>.trans (half_range hp).2
    have normal_angle : angle p (direction p) ≤ x := by
      apply (angle_le_iff_cos_mul_norm_le pn zn x_nonneg (by linarith only [x_upper, pi_pos])).2
      rw [unit, mul_one, ← real_inner_comm p (direction p), at_side hp]
      exact (mul_le_mul_of_nonneg_left (p_range hp).2 cos_pos.le).trans_eq (mul_comm _ _)
    have both : angle z (direction p) ≤ π / 4 + x := by
      exact (angle_le_angle_add_angle z p (direction p)).trans
        (add_le_add ((angle_comm z p).trans_le limit) normal_angle)
    have bound := (angle_le_iff_cos_mul_norm_le zero zn (by positivity : 0 ≤ π / 4 + x)
      (by linarith only [x_upper, pi_pos])).1 both
    rw [unit, mul_one] at bound
    exact (mul_le_mul_of_nonneg_right exit_margin
      (norm_nonneg _)).trans bound

/-- The small-step bounds are a special case of the aperture and exit criteria. -/
theorem roundSelector_aperture_of_small_step {a x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (x_nonneg : 0 ≤ x) (mesh : x ^ 2 ≤ a / 4) :
    x ≤ π / 6 ∧ 1 / (√2 * cos x) < cos (π / 4 - 0.49 * a) ∧
      0.48 * a ≤ cos (π / 4 + x) := by
  have a_upper : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have x_upper : x < 0.363 := by nlinarith only [a_upper, mesh, sq_nonneg (x - 0.363)]
  have narrower := round_selector_cone_ratio_lt positive small x_nonneg mesh
  have comparison : cos (π / 4 - a / 4) ≤ cos (π / 4 - 0.49 * a) :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith only [small, pi_pos])
      (by linarith only [positive, pi_pos]) (by linarith only [positive])
  exact ⟨by linarith only [x_upper, pi_gt_d2], narrower.trans_le comparison,
    (round_selector_margin positive small x_nonneg mesh).2.1⟩

/-- The original small-step criterion for adaptive round selector routing. -/
theorem exists_roundSelectorRouting {I : Type*} [Finite I] [Nonempty I]
    {slopes : Set Plane} (B : PolygonSideDirections I slopes)
    (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
    (boundary : (frontier slopes).Nonempty)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    {a x radius : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (x_nonneg : 0 ≤ x) (mesh : x ^ 2 ≤ a / 4) (radius_pos : 0 < radius)
    (side_distance : ∀ i, B.offset i = radius * cos x)
    (radius_bound : ∀ p ∈ slopes, ‖p‖ ≤ radius)
    (angles : ∀ f, K.normalSlope f ∈ slopes → ∀ i,
      (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 0.99 * a) :
    let progress := radius / √2
    Nonempty (K.CompatibleAdaptiveRouting {f | K.normalSlope f ∈ slopes}
      (K.clippedExtension slopes compact nonempty) boundary
      (Metric.closedBall (0 : Plane) progress) progress (sin (0.495 * a)) (0.48 * a)) := by
  obtain ⟨x_upper, aperture, exit_margin⟩ := roundSelector_aperture_of_small_step positive small x_nonneg mesh
  exact K.exists_roundSelectorRouting_of_aperture B compact nonempty boundary no_boundary positive small
    x_nonneg x_upper aperture exit_margin radius_pos side_distance radius_bound angles

end Unfoldings.ConvexRoof
