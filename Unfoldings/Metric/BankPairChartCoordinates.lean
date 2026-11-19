module

public import Unfoldings.Metric.BankPairNeighborhood
public import Unfoldings.Metric.BallFromLocalSteps

/-! Coordinates on the two original neighborhoods of a seam with half-disk charts. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

/-- A closed half-disk inside an open disk, with the common diameter on both sides. -/
def bankHalfDisk (side : Bool) (r : ℝ) : Set ℂ :=
  Metric.ball 0 r ∩ {z | if side then z.im ≤ 0 else 0 ≤ z.im}

variable {I : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]

/-- Two suitably separated original centers and their normalized metric charts. -/
structure BankPairChart (a : Bool → Total X) (r : ℝ) where
  positive : 0 < r
  separated : ENNReal.ofReal (4 * r) ≤ faceCost X (a false) (a true)
  chart : ∀ side, Metric.eball (a side).2 (ENNReal.ofReal r) ≃ᵢ bankHalfDisk side r
  centered : ∀ side, (chart side ⟨_, Metric.mem_eball_self
    (ENNReal.ofReal_pos.mpr positive)⟩).val = 0

namespace BankPairChart

variable {X} {a : Bool → Total X} {r : ℝ} (C : BankPairChart X a r)

/-- The exact intrinsic radius in a tagged original bank neighborhood. -/
def Near (_C : BankPairChart X a r) (side : Bool) (b : Total X) : Prop :=
  faceCost X (a side) b < ENNReal.ofReal r

theorem near_iff (side : Bool) (b : Total X) :
    C.Near side b ↔ ∃ equal : b.1 = (a side).1,
      edist (equal ▸ b.2) (a side).2 < ENNReal.ofReal r := by
  classical
  obtain ⟨i, b⟩ := b
  unfold Near
  by_cases equal : i = (a side).1
  · subst i
    simp [faceCost, edist_comm]
  · simp [faceCost, equal, Ne.symm equal]

theorem not_near_other {side : Bool} {b : Total X} (near : C.Near side b) :
    ¬ C.Near (!side) b := by
  intro other
  have separation : ENNReal.ofReal (4 * r) ≤ faceCost X (a side) (a (!side)) := by
    cases side
    · exact C.separated
    · rw [faceCost_comm]
      exact C.separated
  have next := (faceCost_triangle X (a side) b (a (!side))).trans_lt
    (ENNReal.add_lt_add near (show faceCost X b (a (!side)) < ENNReal.ofReal r from
      (faceCost_comm X _ _).trans_lt other))
  have radius : ENNReal.ofReal r + ENNReal.ofReal r ≤ ENNReal.ofReal (4 * r) := by
    rw [← ENNReal.ofReal_add C.positive.le C.positive.le]
    exact ENNReal.ofReal_le_ofReal (by linarith [C.positive])
  exact (not_lt_of_ge separation) (next.trans_le radius)

/-- Lift a point of the original extended-metric ball to its tagged piece. -/
def tagged (_C : BankPairChart X a r) (side : Bool)
    (b : Metric.eball (a side).2 (ENNReal.ofReal r)) : Total X :=
  ⟨(a side).1, b.val⟩

theorem near_tagged (side : Bool) (b : Metric.eball (a side).2 (ENNReal.ofReal r)) :
    C.Near side (C.tagged side b) :=
  (C.near_iff side _).mpr ⟨rfl, b.property⟩

/-- Recover the intrinsic original point from a tagged point in its neighborhood. -/
def nearPoint (side : Bool) (b : Total X) (near : C.Near side b) :
    Metric.eball (a side).2 (ENNReal.ofReal r) :=
  ⟨(C.near_iff side b).mp near |>.choose ▸ b.2,
    ((C.near_iff side b).mp near).choose_spec⟩

theorem tagged_nearPoint (side : Bool) (b : Total X) (near : C.Near side b) :
    C.tagged side (C.nearPoint side b near) = b := by
  obtain ⟨i, b⟩ := b
  have same := ((C.near_iff side ⟨i,b⟩).mp near).choose
  change i = (a side).1 at same
  subst i
  rfl

theorem nearPoint_tagged (side : Bool) (b : Metric.eball (a side).2 (ENNReal.ofReal r))
    (near : C.Near side (C.tagged side b)) : C.nearPoint side (C.tagged side b) near = b := rfl

/-- Coordinates agree with the appropriate original chart on its whole neighborhood. -/
def coordinates (b : Total X) : ℂ := by
  classical
  exact if left : C.Near false b then (C.chart false (C.nearPoint false b left)).val
    else if right : C.Near true b then (C.chart true (C.nearPoint true b right)).val else 0

theorem coordinates_tagged (side : Bool) (b : Metric.eball (a side).2 (ENNReal.ofReal r)) :
    C.coordinates (C.tagged side b) = (C.chart side b).val := by
  classical
  have near := C.near_tagged side b
  cases side
  · simp only [coordinates, dite_eq_left near, C.nearPoint_tagged]
  · have outside : ¬ C.Near false (C.tagged true b) := C.not_near_other near
    simp only [coordinates, dite_eq_right outside, dite_eq_left near, C.nearPoint_tagged]

theorem coordinates_near (side : Bool) (b : Total X) (near : C.Near side b) :
    C.coordinates b = (C.chart side (C.nearPoint side b near)).val :=
  (congrArg C.coordinates (C.tagged_nearPoint side b near)).symm.trans
    (C.coordinates_tagged side _)

theorem coordinates_mem_ball (side : Bool) (b : Total X) (near : C.Near side b) :
    C.coordinates b ∈ Metric.ball (0 : ℂ) r := by
  rw [C.coordinates_near side b near]
  exact (C.chart side (C.nearPoint side b near)).property.1

end BankPairChart
end Unfoldings.MetricGluing
