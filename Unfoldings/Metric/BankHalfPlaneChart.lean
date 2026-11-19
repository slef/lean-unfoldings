module

public import Unfoldings.Metric.BankPairChartCoordinates
public import Unfoldings.Metric.CenteredBallRestriction

/-! Normalize original bank chart coordinates and restrict their radii. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

/-- The two standard closed half-planes about the real axis. -/
def bankHalfPlane (side : Bool) : Set ℂ :=
  {z | if side then z.im ≤ 0 else 0 ≤ z.im}

/-- The origin belongs to either closed half-plane. -/
def bankHalfPlaneOrigin (side : Bool) : bankHalfPlane side :=
  ⟨0, by cases side <;> exact (show (0 : ℝ) ≤ 0 from le_rfl)⟩

/-- The corresponding whole ball in the half-plane metric is the original half-disk. -/
def bankHalfPlaneBallIsometry (side : Bool) (r : ℝ) :
    Metric.eball (bankHalfPlaneOrigin side) (ENNReal.ofReal r) ≃ᵢ bankHalfDisk side r where
  toFun z := ⟨z.val.val, by
    have near : edist z.val (bankHalfPlaneOrigin side) < ENNReal.ofReal r := z.property
    rw [edist_dist] at near
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mp near, z.val.property⟩
  invFun z := ⟨⟨z.val, z.property.2⟩, by
    rw [Metric.mem_eball, edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr z.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  isometry_toFun _ _ := rfl

@[simp] theorem bankHalfPlaneBallIsometry_val (side : Bool) (r : ℝ)
    (z : Metric.eball (bankHalfPlaneOrigin side) (ENNReal.ofReal r)) :
    (bankHalfPlaneBallIsometry side r z).val = z.val.val := rfl

/-- A chart of a bank is normalized when increasing time moves along the positive real
axis at the original speed. Either occupied half-plane can be chosen by reflection. -/
structure BankHalfPlaneChart {A X : Type*} [EMetricSpace X]
    (bank : A → X) (t : A) (side : Bool) (realCoord : A → ℝ) (r : ℝ) where
  positive : 0 < r
  chart : Metric.eball (bank t) (ENNReal.ofReal r) ≃ᵢ
    Metric.eball (bankHalfPlaneOrigin side) (ENNReal.ofReal r)
  centered : (chart ⟨bank t, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩).val =
    bankHalfPlaneOrigin side
  parameter : ∀ s (near : bank s ∈ Metric.eball (bank t) (ENNReal.ofReal r)),
    (chart ⟨bank s, near⟩).val.val = (realCoord s : ℂ)

namespace BankHalfPlaneChart

variable {A X : Type*} [EMetricSpace X] {bank : A → X} {t : A} {side : Bool}
  {coord : A → ℝ} {R : ℝ} (C : BankHalfPlaneChart bank t side coord R)

/-- A smaller centered ball keeps the same exact original bank coordinates. -/
def restrict {r : ℝ} (positive : 0 < r) (small : r ≤ R) :
    BankHalfPlaneChart bank t side coord r where
  positive := positive
  chart := restrictCenteredEBallEquiv (ENNReal.ofReal_pos.mpr C.positive)
    (ENNReal.ofReal_le_ofReal small) C.chart C.centered
  centered := C.centered
  parameter s near := C.parameter s (near.trans_le (ENNReal.ofReal_le_ofReal small))

end BankHalfPlaneChart
end Unfoldings.MetricGluing
