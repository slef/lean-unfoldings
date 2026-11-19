module

public import Unfoldings.Metric.CenteredBallRestriction
public import Unfoldings.Metric.BallChart

/-! Whole-ball regularity transfers through a centered local ball isometry. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings

variable {X Y E : Type*} [EMetricSpace X] [EMetricSpace Y] [MetricSpace E]

/-- Recenter a model chart at the actual image of the source center before restricting.
No assertion that a pre-existing ball chart sends centers to centers is needed. -/
def recenterRestrictedBallChart {x : X} {c : E} {R r : ℝ} (positive : 0 < R)
    (small : r ≤ R) (B : Metric.eball x (ENNReal.ofReal R) ≃ᵢ Metric.ball c R)
    (cover : Metric.ball (B ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val r ⊆
      Metric.ball c R) :
    Metric.eball x (ENNReal.ofReal r) ≃ᵢ
      Metric.ball (B ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val r := by
  let root : Metric.eball x (ENNReal.ofReal R) :=
    ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩
  let f (z : Metric.eball x (ENNReal.ofReal r)) : Metric.ball (B root).val r :=
    ⟨(B ⟨z.val, z.property.trans_le (ENNReal.ofReal_le_ofReal small)⟩).val, by
      have distance := B.isometry.edist_eq
        ⟨z.val, z.property.trans_le (ENNReal.ofReal_le_ofReal small)⟩ root
      have near : edist (B ⟨z.val, z.property.trans_le
          (ENNReal.ofReal_le_ofReal small)⟩).val (B root).val < ENNReal.ofReal r :=
        distance.trans_lt z.property
      have real_near := (edist_dist _ _).symm.trans_lt near
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp real_near⟩
  have isometric : Isometry f := fun z w => B.isometry _ _
  have onto : Function.Surjective f := by
    intro z
    let target : Metric.ball c R := ⟨z.val, cover z.property⟩
    let q := B.symm target
    have near : edist q.val x < ENNReal.ofReal r := by
      have distance := B.isometry.edist_eq q root
      rw [B.apply_symm_apply] at distance
      have close : edist target.val (B root).val < ENNReal.ofReal r := by
        exact (edist_dist _ _).trans_lt
          ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr z.property)
      exact distance.symm.trans_lt close
    refine ⟨⟨q.val, near⟩, ?_⟩
    apply Subtype.ext
    change (B (B.symm target)).val = target.val
    exact congrArg Subtype.val (B.apply_symm_apply target)
  exact ⟨Equiv.ofBijective f ⟨isometric.injective, onto⟩, isometric⟩

/-- A centered isometry of whole local balls transfers intrinsic metric regularity.
Only the supplied comparison is centered; the original model chart may be unnormalized. -/
theorem HasMetricBallChart.of_centered_ball_equiv {x : X} {y : Y} {R : ℝ}
    (regular : HasMetricBallChart E x) (positive : 0 < R)
    (A : Metric.eball x (ENNReal.ofReal R) ≃ᵢ Metric.eball y (ENNReal.ofReal R))
    (center : (A ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val = y) :
    HasMetricBallChart E y := by
  obtain ⟨δ, δpos, c, ⟨B⟩⟩ := regular
  let root : Metric.eball x (ENNReal.ofReal δ) :=
    ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr δpos)⟩
  obtain ⟨ε, εpos, cover⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball (B root).val (B root).property
  let r := min R (min δ ε)
  have rpos : 0 < r := lt_min positive (lt_min δpos εpos)
  let first := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr positive)
    (ENNReal.ofReal_le_ofReal (min_le_left R (min δ ε))) A center
  let last := recenterRestrictedBallChart δpos
    ((min_le_right R (min δ ε)).trans (min_le_left δ ε)) B
    ((Metric.ball_subset_ball ((min_le_right R (min δ ε)).trans (min_le_right δ ε))).trans cover)
  exact ⟨r, rpos, (B root).val, ⟨first.symm.trans last⟩⟩

end Unfoldings
