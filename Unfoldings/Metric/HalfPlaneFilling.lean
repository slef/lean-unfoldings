module

public import Unfoldings.Basic
public import Unfoldings.Metric.ConvexCover

/-! The original two closed half-disks preserve a common distance bound when filled together. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

variable {X : Type*} [EMetricSpace X]

/-- A filling of a plane ball that is nonexpanding on each closed half-disk is
nonexpanding on the whole ball. The actual target may have other components at infinity. -/
theorem halfPlane_filling_lipschitz {r : ℝ} (fill : Metric.ball (0 : ℂ) r → X)
    (upper : LipschitzOnWith 1 fill {z | 0 ≤ z.val.im})
    (lower : LipschitzOnWith 1 fill {z | z.val.im ≤ 0}) : LipschitzWith 1 fill := by
  let pieces : Bool → Set (Metric.ball (0 : ℂ) r) := fun side =>
    if side then {z | z.val.im ≤ 0} else {z | 0 ≤ z.val.im}
  have closed (side : Bool) : IsClosed (pieces side) := by
    have coordinate : Continuous (fun z : Metric.ball (0 : ℂ) r => z.val.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    cases side
    · exact isClosed_le continuous_const coordinate
    · exact isClosed_le coordinate continuous_const
  have cover : ⋃ side, pieces side = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases le_total 0 z.val.im with above | below
    · exact Set.mem_iUnion.mpr ⟨false, above⟩
    · exact Set.mem_iUnion.mpr ⟨true, below⟩
  exact convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
    (Metric.ball (0 : ℂ) r) (convex_ball _ _) pieces closed cover fill 1
      (fun side => by
        cases side
        · exact upper
        · exact lower)

end Unfoldings
