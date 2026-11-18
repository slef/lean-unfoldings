module

public import Unfoldings.Geometry.OpeningZero

/-! Flat original vertices contribute no rotation and can be removed from opening lists. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

open Classical in
/-- Retain the original event order and remove precisely zero-angle openings. -/
def withoutZeroOpenings (events : List (Opening n)) : List (Opening n) :=
  events.filter (fun event => decide (event.angle ≠ 0))

@[simp] theorem withoutZeroOpenings_heading (events : List (Opening n)) (i : Fin n) :
    openingHeading (withoutZeroOpenings events) i = openingHeading events i := by
  classical
  induction events with
  | nil => rfl
  | cons event events ih =>
    by_cases zero : event.angle = 0
    · simpa only [withoutZeroOpenings, List.filter_cons, zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, openingHeading, List.map_cons, List.sum_cons,
        ite_self, zero_add] using ih
    · simpa only [withoutZeroOpenings, List.filter_cons, decide_eq_true zero, ite_true,
        openingHeading, List.map_cons, List.sum_cons] using congrArg
          (fun value => (if event.hinge ≤ i.castSucc then event.angle else 0) + value) ih

@[simp] theorem withoutZeroOpenings_tailHeading (events : List (Opening n)) :
    openingTailHeading (withoutZeroOpenings events) = openingTailHeading events := by
  classical
  induction events with
  | nil => rfl
  | cons event events ih =>
    by_cases zero : event.angle = 0
    · simpa only [withoutZeroOpenings, List.filter_cons, zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, openingTailHeading,
        List.map_cons, List.sum_cons,
        zero_add] using ih
    · simpa only [withoutZeroOpenings, List.filter_cons, decide_eq_true zero, ite_true,
        openingTailHeading, List.map_cons, List.sum_cons] using congrArg (event.angle + ·) ih

@[simp] theorem withoutZeroOpenings_budget (events : List (Opening n)) :
    openingBudget (withoutZeroOpenings events) = openingBudget events := by
  classical
  induction events with
  | nil => rfl
  | cons event events ih =>
    by_cases zero : event.angle = 0
    · simpa only [withoutZeroOpenings, List.filter_cons, zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, openingBudget, List.map_cons, List.sum_cons,
        abs_zero, zero_add] using ih
    · simpa only [withoutZeroOpenings, List.filter_cons, decide_eq_true zero, ite_true,
        openingBudget, List.map_cons, List.sum_cons] using congrArg (|event.angle| + ·) ih

/-- Removing flat charges retains every literal vertex of the opened finite bank. -/
theorem openings_withoutZero (P : PolygonalChain ℂ n) (events : List (Opening n)) :
    P.openings (withoutZeroOpenings events) = P.openings events := by
  classical
  induction events generalizing P with
  | nil => rfl
  | cons event events ih =>
    by_cases zero : event.angle = 0
    · simpa only [withoutZeroOpenings, List.filter_cons, zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, openings, List.foldl_cons,
        P.rotateSuffix_zero] using ih P
    · simpa only [withoutZeroOpenings, List.filter_cons, decide_eq_true zero, ite_true,
        openings, List.foldl_cons] using ih (P.rotateSuffix event.hinge event.angle)

/-- Nonnegative original charges become strictly positive events after removing flat vertices. -/
theorem withoutZeroOpenings_positive (events : List (Opening n))
    (nonnegative : ∀ event ∈ events, 0 ≤ event.angle)
    (event : Opening n) (member : event ∈ withoutZeroOpenings events) : 0 < event.angle := by
  classical
  have filtered := List.mem_filter.mp member
  have nonzero : event.angle ≠ 0 := of_decide_eq_true filtered.2
  exact lt_of_le_of_ne (nonnegative event filtered.1) nonzero.symm

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ}

/-- Every translated bank point and its entire infinite tail survive removal of flat charges. -/
theorem openings_withoutZero (R : PolygonalRay ℂ n) (events : List (Opening n)) :
    R.openings (withoutZeroOpenings events) = R.openings events := by
  classical
  induction events generalizing R with
  | nil => rfl
  | cons event events ih =>
    by_cases zero : event.angle = 0
    · simpa only [withoutZeroOpenings, List.filter_cons, zero, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, openings, List.foldl_cons,
        R.rotateSuffix_zero] using ih R
    · simpa only [withoutZeroOpenings, List.filter_cons, decide_eq_true zero, ite_true,
        openings, List.foldl_cons] using ih (R.rotateSuffix event.hinge event.angle)

end Unfoldings.PolygonalRay
