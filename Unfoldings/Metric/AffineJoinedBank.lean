module

public import Unfoldings.Metric.JoinedBankParameters
public import Unfoldings.Metric.ForwardBankParameter
public import Unfoldings.Metric.PositiveClosedInterval
public import Unfoldings.Metric.BankHalfPlaneChart

/-! A single affinely parametrized bank chart extends across the join of its finite and infinite descriptions. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.MetricGluing

local notation "zero" => (⟨0, by norm_num⟩ : BankJoinTime)

/-- Join the actual finite and infinite parts of the same forward track. -/
def affineJoinTime (a b : ℝ) (nonnegative : 0 ≤ a) (order : a ≤ b) (s : BankJoinTime) : ℝ≥0 :=
  ⟨b + (b - a) * s.val, by
    have lo : -1 ≤ s.val := s.property
    nlinarith only [nonnegative, mul_le_mul_of_nonneg_left lo (sub_nonneg.mpr order)]⟩

theorem joinedBank_eq_affineJoinTime {X : Type*} (bank : ℝ≥0 → X)
    (a b : ℝ) (nonnegative : 0 ≤ a) (order : a ≤ b) (s : BankJoinTime) :
    joinedBank (fun t => bank (nonnegativeIntervalLineMap a b nonnegative order t))
      (fun t => bank (forwardBankParameter ⟨b, nonnegative.trans order⟩
        ⟨b - a, sub_nonneg.mpr order⟩ t)) s =
      bank (affineJoinTime a b nonnegative order s) := by
  unfold joinedBank
  split <;> apply congrArg bank <;> apply Subtype.ext
  · change a + (1 + s.val) * (b - a) = b + (b - a) * s.val
    ring
  · change b + (b - a) * s.val = b + (b - a) * s.val
    rfl

/-- Original signed arclength is recovered across both parameter ranges. -/
theorem edist_affineJoinTime {X : Type*} [EMetricSpace X] (bank : ℝ≥0 → X)
    (a b : ℝ) (nonnegative : 0 ≤ a) (order : a ≤ b) (speed : ℝ≥0)
    (metric : ∀ s t, edist (bank s) (bank t) = (speed : ℝ≥0∞) * edist s t)
    (s : BankJoinTime) :
    edist (bank (affineJoinTime a b nonnegative order zero))
      (bank (affineJoinTime a b nonnegative order s)) =
      ENNReal.ofReal (|s.val| * ((b - a) * speed.val)) := by
  rw [metric, edist_dist]
  change (speed : ℝ≥0∞) * ENNReal.ofReal |(b + (b - a) * (0 : ℝ)) - (b + (b - a) * s.val)| =
    ENNReal.ofReal (|s.val| * ((b - a) * speed.val))
  rw [show b + (b - a) * (0 : ℝ) - (b + (b - a) * s.val) = (b - a) * (-s.val) by ring,
    abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr order)]
  calc
    _ = ENNReal.ofReal speed.val * ENNReal.ofReal ((b - a) * |s.val|) :=
      congrArg (· * ENNReal.ofReal ((b - a) * |s.val|)) (ENNReal.ofReal_coe_nnreal (p := speed)).symm
    _ = ENNReal.ofReal (speed.val * ((b - a) * |s.val|)) :=
      (ENNReal.ofReal_mul (p := speed.val) speed.property).symm
    _ = _ := congrArg ENNReal.ofReal (by ring)

/-- A normalized half-plane chart at the physical join uses the signed arclength
of the joined bank on both its finite and infinite part. -/
theorem exists_affineJoinedBank_chart {X : Type*} [EMetricSpace X] {finite : unitInterval → X}
    {tail bank : ℝ≥0 → X} {a b : ℝ} (nonnegative : 0 ≤ a) (order : a ≤ b)
    (finite_eq : ∀ t, finite t = bank (nonnegativeIntervalLineMap a b nonnegative order t))
    (tail_eq : ∀ t, tail t = bank (forwardBankParameter ⟨b, nonnegative.trans order⟩
      ⟨b - a, sub_nonneg.mpr order⟩ t))
    (speed : ℝ≥0) (occupied : Bool) (r : ℝ)
    (C : BankHalfPlaneChart bank ⟨b, nonnegative.trans order⟩ occupied
      (fun s : ℝ≥0 => (s.val - b) * speed.val) r) :
    Nonempty (BankHalfPlaneChart (joinedBank finite tail) zero occupied
      (fun s : BankJoinTime => s.val * ((b - a) * speed.val)) r) := by
  let join := joinedBank finite tail
  let center : ℝ≥0 := ⟨b, nonnegative.trans order⟩
  have follows (s : BankJoinTime) : join s = bank (affineJoinTime a b nonnegative order s) := by
    dsimp only [join]
    rw [show finite = _ from funext finite_eq, show tail = _ from funext tail_eq]
    exact joinedBank_eq_affineJoinTime bank a b nonnegative order s
  have z_time : affineJoinTime a b nonnegative order zero = center :=
    Subtype.ext (by change b + (b - a) * 0 = b; ring)
  have same : join zero = bank center := (follows zero).trans (congrArg bank z_time)
  let move := basedEBallIsometry (IsometryEquiv.refl X) (join zero) (bank center) same
    (ENNReal.ofReal r)
  refine ⟨⟨C.positive, move.trans C.chart, ?_, ?_⟩⟩
  · change (C.chart (move _)).val = _
    have eq : move ⟨join zero, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩ =
        ⟨bank center, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩ := Subtype.ext same
    rw [eq, C.centered]
  · intro s near
    let t := affineJoinTime a b nonnegative order s
    have it_is_near : bank t ∈ Metric.eball (bank center) (ENNReal.ofReal r) := by
      rw [← follows s, ← same]
      exact near
    have moved : move ⟨join s, near⟩ = ⟨bank t, it_is_near⟩ := Subtype.ext (follows s)
    change (C.chart (move _)).val.val = _
    rw [moved, C.parameter t it_is_near]
    apply congrArg Complex.ofReal
    change (b + (b - a) * s.val - b) * speed.val = _
    ring

end Unfoldings.MetricGluing
