module

public import Unfoldings.Topology.OrderedChanges
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

/-!
# Signed horizontal-ray crossings of coordinate-monotone chains

Only changes of the level indicator contribute. Equality with the level is
handled by a half-open convention; horizontal and collinear edges contribute
zero. Crossing positions along a coordinate-monotone chain are ordered, so
signed crossings cancel before any estimate is made.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Half-open upper-level indicator; this is a signed-count device, not a noncrossing test. -/
def levelIndicator (level value : ℝ) : ℝ := if level < value then 1 else 0

theorem levelIndicator_bounds (level value : ℝ) :
    levelIndicator level value ∈ Set.Icc (0 : ℝ) 1 := by
  unfold levelIndicator
  split_ifs <;> constructor <;> norm_num

theorem levelIndicator_monotone (level : ℝ) : Monotone (levelIndicator level) := by
  intro a b le
  by_cases first : level < a
  · have last := first.trans_le le
    change (if level < a then (1 : ℝ) else 0) ≤ if level < b then 1 else 0
    rw [ite_eq_left first, ite_eq_left last]
  · change (if level < a then (1 : ℝ) else 0) ≤ levelIndicator level b
    rw [ite_eq_right first]
    exact (levelIndicator_bounds level b).1

/-- The affine parameter at which a nonhorizontal segment reaches the requested level. -/
def levelCrossingParameter (a b level : ℝ) : ℝ := (level - a) / (b - a)

theorem levelCrossingParameter_bounds {a b level : ℝ}
    (change : levelIndicator level b ≠ levelIndicator level a) :
    levelCrossingParameter a b level ∈ Set.Icc (0 : ℝ) 1 := by
  have rising {a b : ℝ} (first : a ≤ level) (last : level < b) :
      levelCrossingParameter a b level ∈ Set.Icc (0 : ℝ) 1 := by
    have positive : 0 < b - a := by linarith
    exact ⟨div_nonneg (sub_nonneg.mpr first) positive.le,
      (div_le_one positive).mpr (by linarith)⟩
  by_cases first : level < a <;> by_cases last : level < b
  · simp only [levelIndicator, ite_eq_left first, ite_eq_left last, ne_eq, not_true_eq_false]
      at change
  · have reverse := rising (le_of_not_gt last) first
    have parameter : levelCrossingParameter a b level =
        1 - levelCrossingParameter b a level := by
      unfold levelCrossingParameter
      have different : a - b ≠ 0 := by linarith
      have other : b - a ≠ 0 := by linarith
      field_simp [different, other]
      nlinarith
    rw [parameter]
    constructor <;> linarith [reverse.1, reverse.2]
  · exact rising (le_of_not_gt first) last
  · simp only [levelIndicator, ite_eq_right first, ite_eq_right last, ne_eq, not_true_eq_false]
      at change

/-- The chosen affine parameter is an actual intersection with the requested horizontal line. -/
theorem levelCrossingParameter_hits {a b level : ℝ}
    (change : levelIndicator level b ≠ levelIndicator level a) :
    (1 - levelCrossingParameter a b level) * a + levelCrossingParameter a b level * b = level := by
  have different : b - a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro same
    exact change (congrArg (levelIndicator level) same)
  unfold levelCrossingParameter
  field_simp [different]
  ring

/-- The actual horizontal coordinate of the level intersection whenever the indicator changes. -/
def levelCrossingPosition {n : ℕ} (x y : Fin (n + 1) → ℝ) (level : ℝ) (i : Fin n) : ℝ :=
  (1 - levelCrossingParameter (y i.castSucc) (y i.succ) level) * x i.castSucc +
    levelCrossingParameter (y i.castSucc) (y i.succ) level * x i.succ

/-- A coordinate-monotone chain orders the horizontal positions of all genuine indicator changes. -/
theorem levelCrossingPosition_ordered {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (monotone : Monotone x) (level : ℝ) (i j : Fin n) (le : i ≤ j)
    (first : levelIndicator level (y i.succ) ≠ levelIndicator level (y i.castSucc))
    (last : levelIndicator level (y j.succ) ≠ levelIndicator level (y j.castSucc)) :
    levelCrossingPosition x y level i ≤ levelCrossingPosition x y level j := by
  have bounds (k : Fin n) (change : levelIndicator level (y k.succ) ≠
        levelIndicator level (y k.castSucc)) :
      x k.castSucc ≤ levelCrossingPosition x y level k ∧
        levelCrossingPosition x y level k ≤ x k.succ := by
    have parameter := levelCrossingParameter_bounds change
    have step := monotone (Fin.castSucc_le_succ k)
    dsimp only [levelCrossingPosition]
    constructor <;> nlinarith [parameter.1, parameter.2]
  by_cases same : i = j
  · subst j
    exact le_rfl
  · have gap : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      have values := Fin.le_iff_val_le_val.mp le
      have different : i.val ≠ j.val := fun equal => same (Fin.ext equal)
      omega
    exact (bounds i first).2.trans ((monotone gap).trans (bounds j last).1)

/-- A signed crossing of the horizontal ray starting at `(cut, level)`. -/
def horizontalRayCrossing {n : ℕ} (x y : Fin (n + 1) → ℝ) (cut level : ℝ) (i : Fin n) : ℝ :=
  if cut < levelCrossingPosition x y level i then
    levelIndicator level (y i.succ) - levelIndicator level (y i.castSucc) else 0

/-- All subdivisions and repeated crossings cancel to a signed count of magnitude at most one. -/
theorem abs_sum_horizontalRayCrossing_of_monotone_x {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (monotone : Monotone x) (cut level : ℝ) :
    |∑ i : Fin n, horizontalRayCrossing x y cut level i| ≤ 1 := by
  apply abs_sum_ordered_changes_le_one (fun i => levelIndicator level (y i))
    (fun i => levelIndicator_bounds level (y i))
    (fun i => cut < levelCrossingPosition x y level i)
  intro i j le first last inside
  exact inside.trans_le (levelCrossingPosition_ordered x y monotone level i j le first last)

/-- Reversing horizontal monotonicity reverses the ordering of all nonzero crossings. -/
theorem abs_sum_horizontalRayCrossing_of_antitone_x {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (antitone : Antitone x) (cut level : ℝ) :
    |∑ i : Fin n, horizontalRayCrossing x y cut level i| ≤ 1 := by
  have reverse : Monotone (fun i => -x i) := fun i j le => neg_le_neg (antitone le)
  apply abs_sum_reverse_ordered_changes_le_one (fun i => levelIndicator level (y i))
    (fun i => levelIndicator_bounds level (y i))
    (fun i => cut < levelCrossingPosition x y level i)
  intro i j le first last inside
  have ordered := levelCrossingPosition_ordered (fun k => -x k) y reverse level i j le first last
  have negative (k : Fin n) : levelCrossingPosition (fun k => -x k) y level k =
      -levelCrossingPosition x y level k := by
    unfold levelCrossingPosition
    ring
  rw [negative, negative] at ordered
  exact inside.trans_le (by linarith)

/-- A vertically monotone chain also has signed ray-crossing count of magnitude at most one. -/
theorem abs_sum_horizontalRayCrossing_of_monotone_y {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (monotone : Monotone y) (cut level : ℝ) :
    |∑ i : Fin n, horizontalRayCrossing x y cut level i| ≤ 1 :=
  abs_sum_selected_changes_of_monotone (fun i => levelIndicator level (y i))
    (fun i => levelIndicator_bounds level (y i)) ((levelIndicator_monotone level).comp monotone)
    (fun i => cut < levelCrossingPosition x y level i)

/-- The same cancellation applies to a downward monotone chain. -/
theorem abs_sum_horizontalRayCrossing_of_antitone_y {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (antitone : Antitone y) (cut level : ℝ) :
    |∑ i : Fin n, horizontalRayCrossing x y cut level i| ≤ 1 :=
  abs_sum_selected_changes_of_antitone (fun i => levelIndicator level (y i))
    (fun i => levelIndicator_bounds level (y i))
    (fun _i _j le => levelIndicator_monotone level (antitone le))
    (fun i => cut < levelCrossingPosition x y level i)

end Unfoldings
