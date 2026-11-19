module

public import Unfoldings.Metric.BankGraft
public import Unfoldings.Metric.Unglued

/-! Small route-metric balls at a single attachment stay near its two original centers. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {I A : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]
  {i j : I} (left : A → X i) (right : A → X j)

/-- Identify one pair of original bank curves, allowing both curves in the same piece. -/
def bankPairGlue (a b : Total X) : Prop :=
  ∃ t, a = ⟨i, left t⟩ ∧ b = ⟨j, right t⟩

theorem faceCost_same_tag (i : I) (x y : X i) :
    faceCost X ⟨i, x⟩ ⟨i, y⟩ = edist x y := by
  simp [faceCost]

/-- If the wrong banks stay outside the center neighborhoods, a point near the
joined center has an original representative just as near one of the two centers. -/
theorem bankPair_near_centers (t : A) {δ : ℝ≥0∞}
    (same_metric : ∀ s, edist (left t) (left s) = edist (right t) (right s))
    (clear_left : ∀ s, δ ≤ faceCost X ⟨j, right t⟩ ⟨i, left s⟩)
    (clear_right : ∀ s, δ ≤ faceCost X ⟨i, left t⟩ ⟨j, right s⟩)
    (b : Total X) {r : ℝ≥0∞} (small : r ≤ δ)
    (near : edist (point X (bankPairGlue X left right) ⟨i, left t⟩)
      (point X (bankPairGlue X left right) b) < r) :
    faceCost X ⟨i, left t⟩ b < r ∨ faceCost X ⟨j, right t⟩ b < r := by
  let a : Total X := ⟨i, left t⟩
  let c : Total X := ⟨j, right t⟩
  let height (x : Total X) := min δ (min (faceCost X a x) (faceCost X c x))
  have root : height a = 0 := by simp [height, faceCost, a]
  have seam (s : A) : height ⟨i, left s⟩ = height ⟨j, right s⟩ := by
    have l := clear_left s
    have r := clear_right s
    change δ ≤ faceCost X c ⟨i, left s⟩ at l
    change δ ≤ faceCost X a ⟨j, right s⟩ at r
    dsimp only [height]
    calc
      _ = min (faceCost X a ⟨i, left s⟩) δ := by
        rw [min_left_comm, min_eq_left l]
      _ = min (faceCost X c ⟨j, right s⟩) δ := by
        simp only [a, c, faceCost, same_metric]
      _ = _ := by rw [min_comm _ (faceCost X c _), min_left_comm, min_eq_left r]
  have progress (x y : Total X) :
      height y ≤ height x + stepCost X (bankPairGlue X left right) x y := by
    classical
    by_cases joined : bankPairGlue X left right x y ∨ bankPairGlue X left right y x
    · have equal : height x = height y := by
        rcases joined with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
        · exact seam s
        · exact (seam s).symm
      simp [stepCost, joined, equal]
    · rw [stepCost, ite_eq_right joined]
      change height y ≤ min δ (min (faceCost X a x) (faceCost X c x)) + faceCost X x y
      rcases le_total δ (min (faceCost X a x) (faceCost X c x)) with cap | inside
      · rw [min_eq_left cap]
        exact (min_le_left _ _).trans le_self_add
      · rw [min_eq_right inside]
        rcases le_total (faceCost X a x) (faceCost X c x) with first | last
        · rw [min_eq_left first]
          exact ((min_le_right _ _).trans (min_le_left _ _)).trans (faceCost_triangle X a x y)
        · rw [min_eq_right last]
          exact ((min_le_right _ _).trans (min_le_right _ _)).trans (faceCost_triangle X c x y)
  have bound : height b ≤ edist (point X (bankPairGlue X left right) a)
      (point X (bankPairGlue X left right) b) := by
    change height b ≤ Route.distance (stepCost X (bankPairGlue X left right)) a b
    unfold Route.distance
    apply le_iInf
    intro route
    have along {x y : Total X} (path : Route (Total X) x y) :
        height y ≤ height x + path.length (stepCost X (bankPairGlue X left right)) := by
      induction path with
      | nil => simp
      | cons x y tail ih =>
        exact ih.trans (by
          rw [Route.length, ← add_assoc]
          exact add_le_add (progress x y) le_rfl)
    simpa only [root, zero_add] using along route
  exact min_lt_iff.mp ((min_lt_iff.mp (bound.trans_lt near)).resolve_left (not_lt_of_ge small))

/-- Closedness of each whole bank excludes its points near the other center
unless that center belongs to the bank. This also covers two banks of one piece. -/
theorem exists_bankPair_clearance (t : A)
    (left_closed : IsClosed (Set.range left)) (right_closed : IsClosed (Set.range right))
    (different_left : ∀ s, (⟨j, right t⟩ : Total X) ≠ ⟨i, left s⟩)
    (different_right : ∀ s, (⟨i, left t⟩ : Total X) ≠ ⟨j, right s⟩) :
    ∃ δ > (0 : ℝ≥0∞),
      (∀ s, δ ≤ faceCost X ⟨j, right t⟩ ⟨i, left s⟩) ∧
      (∀ s, δ ≤ faceCost X ⟨i, left t⟩ ⟨j, right s⟩) := by
  classical
  by_cases same : i = j
  · subst j
    have outside_left : right t ∉ Set.range left := by
      rintro ⟨s, equal⟩
      exact different_left s (congrArg (Sigma.mk i) equal.symm)
    have outside_right : left t ∉ Set.range right := by
      rintro ⟨s, equal⟩
      exact different_right s (congrArg (Sigma.mk i) equal.symm)
    obtain ⟨d, dpos, left_ball⟩ := EMetric.isOpen_iff.mp left_closed.isOpen_compl _ outside_left
    obtain ⟨e, epos, right_ball⟩ :=
      EMetric.isOpen_iff.mp right_closed.isOpen_compl _ outside_right
    refine ⟨min d e, lt_min dpos epos, ?_, ?_⟩
    · intro s
      have bound : d ≤ edist (left s) (right t) := by
        by_contra! near
        exact left_ball near ⟨s, rfl⟩
      simpa [faceCost, edist_comm] using (min_le_left d e).trans bound
    · intro s
      have bound : e ≤ edist (right s) (left t) := by
        by_contra! near
        exact right_ball near ⟨s, rfl⟩
      simpa [faceCost, edist_comm] using (min_le_right d e).trans bound
  · exact ⟨1, zero_lt_one, fun _ => by simp [faceCost, Ne.symm same],
      fun _ => by simp [faceCost, same]⟩

end Unfoldings.MetricGluing
