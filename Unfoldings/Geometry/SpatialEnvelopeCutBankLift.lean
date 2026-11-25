module

public import Unfoldings.Geometry.SpatialEnvelopeCutFiber
public import Unfoldings.Metric.LocalIsometricLift
public import Unfoldings.Metric.PositiveHalflineExtension
public import Mathlib.Topology.MetricSpace.Dilation

/-! A closed bank lifts through additional cuts they do not change on its open part. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]
  {cuts single : Set Plane} (included : single ⊆ cuts)

/-- Identical geometric cut germs give both a unique fiber and an isometric
ball transfer at the corresponding original bank point. -/
theorem exists_forgetCut_ball_chart_at (x : P.Cut cuts) {ε : ℝ} (positive : 0 < ε)
    (same : ∀ z, dist z (Cap.horizontal (P.restoreCut cuts x).val) < ε →
      (z ∈ cuts ↔ z ∈ single)) :
    ∃ r > 0, ∃ B : Metric.eball x (ENNReal.ofReal r) ≃ᵢ
        Metric.eball (P.forgetCut cuts single included x) (ENNReal.ofReal r),
      ∀ y, (B y).val = P.forgetCut cuts single included y.val := by
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective (fun a => P.planarCell a) (P.cutGlue cuts) x
  obtain ⟨chart⟩ := P.exists_forgetCut_ball_chart cuts single included a positive same
  exact ⟨chart.radius, chart.positive, chart.chart, chart.agrees⟩

/-- Extra cuts that miss each open bank germ preserve its whole closed metric
bank, including the endpoint obtained by completeness in the larger cut. -/
theorem exists_closedBank_lift (g : ℝ≥0 →ᵈ P.Cut single)
    (germ : ∀ t : ℝ≥0, 0 < t.val → ∃ ε > 0, ∀ z,
      dist z (Cap.horizontal (P.restoreCut single (g t)).val) < ε →
        (z ∈ cuts ↔ z ∈ single)) :
    ∃ lift : ℝ≥0 →ᵈ P.Cut cuts, (∀ t, P.forgetCut cuts single included (lift t) = g t) ∧
      ∀ s t, edist (lift s) (lift t) = edist (g s) (g t) := by
  let F := P.forgetCut cuts single included
  have F_bound := P.forgetCut_lipschitz cuts single included
  let time : Set.Ioi (0 : ℝ) → ℝ≥0 := fun t => ⟨t.val, t.property.le⟩
  have time_rigid : Isometry time := fun _ _ => rfl
  have local_germ (t : Set.Ioi (0 : ℝ)) (x : P.Cut cuts) (image : F x = g (time t)) :
      ∃ ε > 0, ∀ z, dist z (Cap.horizontal (P.restoreCut cuts x).val) < ε →
        (z ∈ cuts ↔ z ∈ single) := by
    have physical : P.restoreCut cuts x = P.restoreCut single (g (time t)) := by
      rw [← image]
      exact (P.restoreCut_forgetCut cuts single included x).symm
    rw [physical]
    exact germ (time t) t.property
  have exists_unique (t : Set.Ioi (0 : ℝ)) : ∃! x, F x = g (time t) := by
    obtain ⟨x, image⟩ := P.forgetCut_surjective cuts single included (g (time t))
    obtain ⟨ε, positive, same⟩ := local_germ t x image
    refine ⟨x, image, fun y hy => ?_⟩
    exact (P.forgetCut_injective_at_of_local_eq cuts single included x positive same y
      (image.trans hy.symm)).symm
  let f (t : Set.Ioi (0 : ℝ)) := (exists_unique t).choose
  have agrees (t : Set.Ioi (0 : ℝ)) : F (f t) = g (time t) := (exists_unique t).choose_spec.1
  obtain ⟨K, K_ne, rigid_g⟩ := g.edist_eq'
  change ∀ s t : ℝ≥0, edist (g s) (g t) = (K : ℝ≥0∞) * edist s t at rigid_g
  have g_bound : LipschitzWith K g := fun s t => (rigid_g s t).le
  have f_bound : LipschitzWith K f := by
    apply lipschitzWith_lift_of_ball_charts (Set.Ioi (0 : ℝ)) (convex_Ioi 0)
      f (g ∘ time) F K
    · simpa only [mul_one] using g_bound.comp time_rigid.lipschitzWith
    · intro t x image
      exact (exists_unique t).choose_spec.2 x image
    · intro t
      obtain ⟨ε, positive, same⟩ := local_germ t (f t) (agrees t)
      obtain ⟨r, r_pos, chart, chart_eq⟩ := P.exists_forgetCut_ball_chart_at included
        (f t) positive same
      refine ⟨r, r_pos, ?_⟩
      change ∃ B : Metric.eball (f t) (ENNReal.ofReal r) ≃ᵢ
          Metric.eball (g (time t)) (ENNReal.ofReal r), ∀ y, (B y).val = F y.val
      rw [← agrees t]
      exact ⟨chart, chart_eq⟩
  let : CompleteSpace (P.Cut cuts) := P.cut_complete cuts
  let h := extendPositiveHalfline f
  have h_bound : LipschitzWith K h := extendPositiveHalfline_lipschitz f f_bound
  have h_eq (t : ℝ≥0) : F (h t) = g t :=
    map_extendPositiveHalfline f f_bound F F_bound.continuous g g_bound.continuous agrees t
  have metric (s t : ℝ≥0) : edist (h s) (h t) = edist (g s) (g t) := by
    rw [rigid_g s t]
    apply le_antisymm (h_bound s t)
    have lower := F_bound (h s) (h t)
    change edist (F (h s)) (F (h t)) ≤ (1 : ℝ≥0∞) * edist (h s) (h t) at lower
    rwa [h_eq s, h_eq t, rigid_g, one_mul] at lower
  exact ⟨⟨h, K, K_ne, fun s t => (metric s t).trans (rigid_g s t)⟩, h_eq, metric⟩

end Unfoldings.SpatialEnvelope.WholePartition
