module

public import Unfoldings.Metric.PolygonalCut
public import Unfoldings.Metric.Excision
public import Unfoldings.Metric.BallChartTransport

/-! Restoring a closed physical cut preserves whole intrinsic balls away from the cut. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts : Set E)

/-- The canonical restoration of all removed physical attachment pieces. -/
theorem cutRestoreInclusion : ∀ a b, (cutSeams cells closed cuts).relation a b →
    (cutSeams cells closed ∅).relation a b :=
  cutSeams_relation_mono cells closed cuts (Set.empty_subset cuts)

/-- Off a closed cut, restoring the cut is an actual whole-ball isometry.
This does not require a development, a manifold premise or bounded cells. -/
theorem exists_cutRestoreChart (cut_closed : IsClosed cuts)
    (a : Total (fun i => cells i)) (outside : a.2.val ∉ cuts) :
    Nonempty (ForgetChart (fun i => cells i) (cutRestoreInclusion cells closed cuts) a) := by
  let S := cutSeams cells closed (∅ : Set E)
  let R := cutSeams cells closed cuts
  obtain ⟨δ, δpos, ball⟩ := Metric.isOpen_iff.mp cut_closed.isOpen_compl a.2.val outside
  have outside_near (b : Total (fun i => cells i))
      (near : edist (point (fun i => cells i) S.relation a)
        (point (fun i => cells i) S.relation b) < ENNReal.ofReal δ) : b.2.val ∉ cuts := by
    have bound := S.fold_lipschitz (point (fun i => cells i) S.relation a)
      (point (fun i => cells i) S.relation b)
    simp only [ENNReal.coe_one, one_mul] at bound
    have physical : edist a.2.val b.2.val < ENNReal.ofReal δ := bound.trans_lt near
    rw [edist_comm, edist_dist] at physical
    exact ball (Metric.mem_ball.mpr
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp physical))
  have local_step (b c : Total (fun i => cells i))
      (hb : edist (point (fun i => cells i) S.relation a)
        (point (fun i => cells i) S.relation b) < ENNReal.ofReal δ)
      (_hc : edist (point (fun i => cells i) S.relation a)
        (point (fun i => cells i) S.relation c) < ENNReal.ofReal δ) :
      edist (point (fun i => cells i) R.relation b) (point (fun i => cells i) R.relation c) ≤
        stepCost (fun i => cells i) S.relation b c := by
    classical
    by_cases joined : S.relation b c ∨ S.relation c b
    · have coordinates : b.2.val = c.2.val := joined.elim
        (fun h => S.physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ h))
        (fun h => (S.physical_eq_of_eqvGen (Relation.EqvGen.rel _ _ h)).symm)
      have equal : point (fun i => cells i) R.relation b =
          point (fun i => cells i) R.relation c :=
        cutSeams_point_eq_of_physical_eq cells closed cuts coordinates (outside_near b hb)
      simp only [stepCost, ite_eq_left joined, equal, edist_self, le_refl]
    · exact (Route.distance_le_cost (stepCost (fun i => cells i) R.relation) b c).trans
        ((stepCost_le_faceCost (fun i => cells i) R.relation b c).trans_eq
          (by rw [stepCost, ite_eq_right joined]))
  have finite : ∀ i, (classIn (fun i => cells i) S.relation a i).Finite :=
    fun i => (S.classIn_subsingleton a i).finite
  obtain ⟨ε, εpos, transport⟩ := S.closedSeams.class_transport a finite
  let r := min ε (δ / 4)
  have rpos : 0 < r := lt_min εpos (div_pos δpos (by norm_num))
  have radial (b : Total (fun i => cells i))
      (near : edist (point (fun i => cells i) S.relation a)
        (point (fun i => cells i) S.relation b) < ENNReal.ofReal r) :
      edist (point (fun i => cells i) R.relation a)
        (point (fun i => cells i) R.relation b) < ENNReal.ofReal r := by
    obtain ⟨q, related, close⟩ := exists_classPoint_of_edist_lt (fun i => cells i) S.relation a
      εpos (min_le_left ε (δ / 4)) finite transport b near
    have equal := cutSeams_point_eq_of_physical_eq cells closed cuts
      (S.physical_eq_of_eqvGen related) outside
    calc
      edist (point (fun i => cells i) R.relation a)
          (point (fun i => cells i) R.relation b) =
          edist (of (fun i => cells i) R.relation b.1 q)
            (of (fun i => cells i) R.relation b.1 b.2) := by rw [equal]; rfl
      _ ≤ edist q b.2 := edist_of_le (fun i => cells i) R.relation b.1 q b.2
      _ < ENNReal.ofReal r := by
        rw [edist_dist, dist_comm]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr close
  have lower (b c : Total (fun i => cells i))
      (hb : edist (point (fun i => cells i) S.relation a)
        (point (fun i => cells i) S.relation b) < ENNReal.ofReal r)
      (hc : edist (point (fun i => cells i) S.relation a)
        (point (fun i => cells i) S.relation c) < ENNReal.ofReal r) :
      edist (point (fun i => cells i) R.relation b) (point (fun i => cells i) R.relation c) ≤
        edist (point (fun i => cells i) S.relation b) (point (fun i => cells i) S.relation c) := by
    apply map_edist_le_edist_of_budget (fun i => cells i) S.relation
      (point (fun i => cells i) R.relation) (point (fun i => cells i) S.relation a)
      (ENNReal.ofReal δ) local_step b c
    have rb := radial b hb
    have rc := radial c hc
    rw [edist_comm] at rb
    have small : 3 * r ≤ δ := by
      have bound : r ≤ δ / 4 := min_le_right _ _
      linarith
    calc
      _ ≤ edist (point (fun i => cells i) S.relation a)
          (point (fun i => cells i) S.relation b) +
          (edist (point (fun i => cells i) R.relation b)
            (point (fun i => cells i) R.relation a) +
          edist (point (fun i => cells i) R.relation a)
            (point (fun i => cells i) R.relation c)) :=
        add_le_add le_rfl (edist_triangle _ _ _)
      _ < ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r) :=
        ENNReal.add_lt_add hb (ENNReal.add_lt_add rb rc)
      _ = ENNReal.ofReal (3 * r) := by
        rw [← ENNReal.ofReal_add rpos.le rpos.le,
          ← ENNReal.ofReal_add rpos.le (add_nonneg rpos.le rpos.le)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal small
  exact ⟨⟨r, rpos, forgetBallIsometry (fun i => cells i) (cutRestoreInclusion cells closed cuts)
    a (ENNReal.ofReal_pos.mpr rpos) lower, fun _ => rfl⟩⟩

variable [NormedSpace ℝ E] {s : Set E}

/-- Restoring the cuts agrees with the physical intrinsic-region map. -/
theorem uncutCoverIsometryEquiv_forget (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (x : PolygonalCut cells closed cuts) :
    uncutCoverIsometryEquiv cells closed convex cover
      (forget (fun i => cells i) (cutRestoreInclusion cells closed cuts) x) =
        cutToPolygonal cells closed cuts convex cover x := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation x
  exact PolygonalPoint.ext rfl

/-- The actual projection onto the uncut intrinsic region preserves a whole metric ball. -/
theorem exists_cutToPolygonal_ball_isometry (convex : ∀ i, Convex ℝ (cells i))
    (cover : s = ⋃ i, cells i) (cut_closed : IsClosed cuts)
    (a : Total (fun i => cells i)) (outside : a.2.val ∉ cuts) :
    ∃ r : ℝ, 0 < r ∧ ∃ A :
      Metric.eball (point (fun i => cells i) (cutSeams cells closed cuts).relation a)
        (ENNReal.ofReal r) ≃ᵢ
      Metric.eball (cutToPolygonal cells closed cuts convex cover
        (point (fun i => cells i) (cutSeams cells closed cuts).relation a)) (ENNReal.ofReal r),
        ∀ x, (A x).val = cutToPolygonal cells closed cuts convex cover x.val := by
  obtain ⟨chart⟩ := exists_cutRestoreChart cells closed cuts cut_closed a outside
  let A := uncutCoverIsometryEquiv cells closed convex cover
  let whole := chart.chart.trans (isometryEquivEBall A
    (point (fun i => cells i) (cutSeams cells closed ∅).relation a)
    (ENNReal.ofReal chart.radius))
  refine ⟨chart.radius, chart.positive, whole, ?_⟩
  intro x
  change A (chart.chart x).val = cutToPolygonal cells closed cuts convex cover x.val
  rw [chart.agrees]
  exact uncutCoverIsometryEquiv_forget cells closed cuts convex cover x.val

end Unfoldings.MetricGluing
