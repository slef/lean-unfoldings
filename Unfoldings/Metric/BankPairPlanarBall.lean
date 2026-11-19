module

public import Unfoldings.Metric.BankPairChartFilling
public import Unfoldings.Metric.BallChart

/-! Two matching original half-plane charts give a planar ball across one bank attachment. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {I A : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)]
  {i j : I} (left : A → X i) (right : A → X j) (t : A)

local notation "Glue" => bankPairGlue X left right
local notation "Center" => fun side : Bool =>
  Bool.rec (Sigma.mk i (left t)) (Sigma.mk j (right t)) side

/-- Matched half-plane charts produce a whole planar ball in the route metric. The banks
may be distinct copies in the same piece. Clearance prevents shortcuts to the other bank. -/
theorem bankPair_planarBall {R r : ℝ} (C : BankPairChart X Center R)
    (positive : 0 < r) (small : 4 * r ≤ R)
    (same_metric : ∀ s, edist (left t) (left s) = edist (right t) (right s))
    (clear_left : ∀ s, ENNReal.ofReal R ≤ faceCost X ⟨j, right t⟩ ⟨i, left s⟩)
    (clear_right : ∀ s, ENNReal.ofReal R ≤ faceCost X ⟨i, left t⟩ ⟨j, right s⟩)
    (matched : ∀ s, C.Near false ⟨i, left s⟩ →
      C.coordinates ⟨i, left s⟩ = C.coordinates ⟨j, right s⟩)
    (diameter : ∀ z : Metric.ball (0 : ℂ) r, ∀ h : z.val.im = 0,
      point X Glue (C.patch (by linarith : r ≤ R) false ⟨z.val, z.property, h.ge⟩) =
        point X Glue (C.patch (by linarith : r ≤ R) true ⟨z.val, z.property, h.le⟩)) :
    HasMetricBallChart ℂ (point X Glue ⟨i, left t⟩) := by
  have included : r ≤ R := by linarith
  have near_copy (b : Total X) {q : ℝ} (bound : q ≤ R)
      (near : edist (point X Glue ⟨i, left t⟩) (point X Glue b) < ENNReal.ofReal q) :
      faceCost X (Center false) b < ENNReal.ofReal q ∨
        faceCost X (Center true) b < ENNReal.ofReal q :=
    bankPair_near_centers X left right t same_metric clear_left clear_right b
      (ENNReal.ofReal_le_ofReal bound) near
  have matched_near (s : A)
      (near : edist (point X Glue ⟨i, left t⟩) (point X Glue ⟨i, left s⟩) <
        ENNReal.ofReal (4 * r)) :
      C.coordinates ⟨i, left s⟩ = C.coordinates ⟨j, right s⟩ := by
    rcases near_copy _ small near with first | last
    · exact matched s (first.trans_le (ENNReal.ofReal_le_ofReal small))
    · exact ((not_lt_of_ge
        ((ENNReal.ofReal_le_ofReal small).trans (clear_left s))) last).elim
  have step (b c : Total X)
      (near_b : edist (point X Glue ⟨i, left t⟩) (point X Glue b) <
        ENNReal.ofReal (4 * r))
      (near_c : edist (point X Glue ⟨i, left t⟩) (point X Glue c) <
        ENNReal.ofReal (4 * r)) :
      edist (C.coordinates b) (C.coordinates c) ≤ stepCost X Glue b c := by
    classical
    by_cases joined : Glue b c ∨ Glue c b
    · have equal : C.coordinates b = C.coordinates c := by
        rcases joined with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
        · exact matched_near s near_b
        · exact (matched_near s near_c).symm
      simp [stepCost, joined, equal]
    · rw [stepCost, ite_eq_right joined]
      have side (x : Total X) (near : edist (point X Glue ⟨i, left t⟩)
          (point X Glue x) < ENNReal.ofReal (4 * r)) : ∃ s, C.Near s x := by
        rcases near_copy x small near with first | last
        · exact ⟨false, first.trans_le (ENNReal.ofReal_le_ofReal small)⟩
        · exact ⟨true, last.trans_le (ENNReal.ofReal_le_ofReal small)⟩
      obtain ⟨s, hb⟩ := side b near_b
      obtain ⟨u, hc⟩ := side c near_c
      exact C.coordinates_edist_le_faceCost s u b c hb hc
  have cover (x : Realization X Glue)
      (near : x ∈ Metric.eball (point X Glue ⟨i, left t⟩) (ENNReal.ofReal r)) :
      ∃ z, C.fill Glue included z = x := by
    obtain ⟨b, rfl⟩ := point_surjective X Glue x
    have radial : edist (point X Glue ⟨i, left t⟩) (point X Glue b) < ENNReal.ofReal r :=
      (edist_comm _ _).trans_lt near
    rcases near_copy b included radial with first | last
    · exact C.fill_of_near Glue included diameter false b first
    · exact C.fill_of_near Glue included diameter true b last
  obtain ⟨B, -⟩ := halfPlane_ball_isometry_of_local_steps X Glue ⟨i, left t⟩ positive
    C.coordinates step (C.fill Glue included)
    (C.fill_lipschitz Glue included diameter false) (C.fill_lipschitz Glue included diameter true)
    (C.fill_center Glue included positive) (C.fill_representatives Glue included) cover
  exact ⟨r, positive, 0, ⟨B.symm⟩⟩

end Unfoldings.MetricGluing
