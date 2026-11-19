module

public import Unfoldings.Metric.BankPairChartCoordinates

/-! The two original bank charts control all nearby direct route steps. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing.BankPairChart

variable {I : Type*} {X : I → Type*} [∀ i, EMetricSpace (X i)]
  {a : Bool → Total X} {r : ℝ} (C : BankPairChart X a r)

theorem coordinates_edist_center (side : Bool) (b : Total X) (near : C.Near side b) :
    edist (C.coordinates b) 0 = faceCost X (a side) b := by
  rw [C.coordinates_near side b near, ← C.centered side]
  let p := C.nearPoint side b near
  have metric := (C.chart side).isometry.edist_eq p
    ⟨(a side).2, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr C.positive)⟩
  change edist ((C.chart side) p).val _ = _
  refine metric.trans ?_
  rw [← C.tagged_nearPoint side b near]
  rw [tagged, faceCost_same_tag]
  exact edist_comm p.val (a side).2

theorem coordinates_edist_le_faceCost (side next : Bool) (b c : Total X)
    (near_b : C.Near side b) (near_c : C.Near next c) :
    edist (C.coordinates b) (C.coordinates c) ≤ faceCost X b c := by
  by_cases same : side = next
  · subst next
    rw [← C.tagged_nearPoint side b near_b, ← C.tagged_nearPoint side c near_c,
      C.coordinates_tagged, C.coordinates_tagged]
    have bound := ((C.chart side).isometry.edist_eq (C.nearPoint side b near_b)
      (C.nearPoint side c near_c)).le
    rw [tagged, tagged, faceCost_same_tag]
    exact bound
  · have sep : ENNReal.ofReal (4 * r) ≤ faceCost X (a side) (a next) := by
      cases side <;> cases next
      · exact (same rfl).elim
      · exact C.separated
      · rw [faceCost_comm]
        exact C.separated
      · exact (same rfl).elim
    have second : faceCost X c (a next) < ENNReal.ofReal r :=
      (faceCost_comm X _ _).trans_lt near_c
    have sum : ENNReal.ofReal r + (ENNReal.ofReal (2 * r) + ENNReal.ofReal r) =
        ENNReal.ofReal (4 * r) := by
      have two : 0 ≤ 2 * r := mul_nonneg (by norm_num) C.positive.le
      rw [← ENNReal.ofReal_add two C.positive.le,
        ← ENNReal.ofReal_add C.positive.le (add_nonneg two C.positive.le)]
      congr 1
      ring
    have cost : ENNReal.ofReal (2 * r) ≤ faceCost X b c := by
      by_contra! short
      have bound := (faceCost_triangle X (a side) b (a next)).trans
        (add_le_add le_rfl (faceCost_triangle X b c (a next)))
      have strict := ENNReal.add_lt_add near_b (ENNReal.add_lt_add short second)
      exact (not_lt_of_ge sep) (bound.trans_lt (strict.trans_eq sum))
    have radial_b := C.coordinates_edist_center side b near_b
    have radial_c := (edist_comm _ _).trans (C.coordinates_edist_center next c near_c)
    apply (edist_triangle _ (0 : ℂ) _).trans
    rw [radial_b, radial_c]
    apply le_trans ((add_le_add near_b.le near_c.le))
    rw [← ENNReal.ofReal_add C.positive.le C.positive.le]
    exact (congrArg ENNReal.ofReal (by ring : r + r = 2 * r)).le.trans cost

end Unfoldings.MetricGluing.BankPairChart
