module

public import Unfoldings.Geometry.StableHalfTurnClosure

/-! A regular half-turn closure in a region fixed before all avoidance constraints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open InnerProductGeometry Real

variable {n : ℕ} (P : PolygonalChain Plane (n + 2)) (source : Plane)

/-- Fix a compact region for all arbitrarily close regular comparisons.
The region is independent of the mesh vertices and lines to be avoided. -/
theorem exists_compact_regular_halfturn_closure
    (radial : P.RadialFrom source 0) (nonzero : ∀ i, P.edge i ≠ 0)
    {γ : ℝ} (positive : 0 < γ)
    (margin : ∀ i, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i))
    (small : (∑ k : Fin n, angle (P.internalSourceRay source k.castSucc)
      (P.internalSourceRay source k.succ)) < π) :
    ∃ region : Set Plane, IsCompact region ∧ Convex ℝ region ∧ Set.range P.path ⊆ region ∧
      ∀ {I A : Type*} [Finite I] [Finite A]
        (point : I → Plane) (equation : A → Plane →ᵃ[ℝ] ℝ) (_proper : ∀ i, equation i ≠ 0)
        {δ : ℝ}, 0 < δ →
        ∃ a b : unitInterval, (0 < a.val ∧ a.val < 1) ∧ (0 < b.val ∧ b.val < 1) ∧
          ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
            let Q := P.trimEnds a b
            dist q source < δ ∧ Q.RadialFrom q 0 ∧
            0 < dist q (Q.vertex 0) ∧
            dist q (Q.vertex 0) < dist q (Q.vertex (Fin.last (n + 2))) ∧
            (∀ z ∈ Set.range Q.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
            0 < inner ℝ (Q.vertex (Fin.last (n + 2)) - q) (c - Q.vertex (Fin.last (n + 2))) ∧
            (∀ i, equation i q ≠ 0 ∧ equation i c ≠ 0) ∧
            (∀ i, Q.vertex 0 ≠ point i ∧ Q.vertex (Fin.last (n + 2)) ≠ point i) ∧
            (∀ (j : Fin 3) (t : ℝ) i,
              let link := radialClosingLinks q (Q.vertex 0) (Q.vertex (Fin.last (n + 2))) c j
              AffineMap.lineMap link.1 link.2 t ≠ point i) ∧
            Schoenflies.IsJordanCurve (Q.threeSegmentClosure q c) ∧
            Q.threeSegmentClosure q c ⊆ region := by
  obtain ⟨U, V, W, T, a, b, c₀, height, open_U, open_V, open_W, open_T, hfirst, hlast,
    source_W, corner_T, stable⟩ := P.exists_stable_halfturn_closure source
      radial nonzero positive margin small
  have compact : IsCompact (Set.range P.path ∪ ({source, c₀} : Set Plane)) :=
    (isCompact_range P.path.continuous).union (Set.Finite.isCompact (by simp))
  obtain ⟨R, cover⟩ := (Metric.isBounded_iff_subset_ball source).mp compact.isBounded
  let ball := Metric.ball source R
  let region := Metric.closedBall source R
  have on_bank : Set.range P.path ⊆ region :=
    (Set.subset_union_left.trans cover).trans Metric.ball_subset_closedBall
  refine ⟨region, isCompact_closedBall _ _, convex_closedBall _ _, on_bank, ?_⟩
  intro I A _ _ point equation proper δ room
  have first_different : P.vertex 0 ≠ P.vertex (0 : Fin (n + 2)).succ :=
    (sub_ne_zero.mp (nonzero 0)).symm
  have last_different : P.vertex (Fin.last (n + 1)).castSucc ≠ P.vertex (Fin.last (n + 2)) :=
    (sub_ne_zero.mp (nonzero (Fin.last (n + 1)))).symm
  obtain ⟨a', first, x_in, x_regular⟩ :=
    exists_open_parameter_avoids_points point open_U first_different a hfirst
  obtain ⟨b', last, y_in, y_regular⟩ :=
    exists_open_parameter_avoids_points point open_V last_different b hlast
  let Q := P.trimEnds a' b'
  let x := Q.vertex 0
  let y := Q.vertex (Fin.last (n + 2))
  have avoid_x (i : I) : x ≠ point i := by
    simpa only [x, Q, P.trimEnds_start, PolygonalChain.point, Fin.castSucc_zero] using x_regular i
  have avoid_y (i : I) : y ≠ point i := by
    simpa only [y, Q, P.trimEnds_last, PolygonalChain.point, Fin.succ_last] using y_regular i
  let sourceEq : A ⊕ I → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim equation (fun i => segmentEquation x (point i))
  have source_proper : ∀ i, sourceEq i ≠ 0 :=
    Sum.rec proper (fun _ => segmentEquation_ne_zero _ _)
  have source_ball : source ∈ ball := cover (Or.inr (by simp))
  obtain ⟨q, ⟨q_W, q_ball⟩, q_regular⟩ :=
    (AffineArrangement.dense_regular sourceEq source_proper).inter_open_nonempty
      (W ∩ ball ∩ Metric.ball source δ)
      ((open_W.inter Metric.isOpen_ball).inter Metric.isOpen_ball)
      ⟨source, ⟨source_W, source_ball⟩, Metric.mem_ball_self room⟩
  let cornerEq : A ⊕ (I ⊕ I) → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim equation (Sum.elim (fun i => segmentEquation q (point i))
      (fun i => segmentEquation y (point i)))
  have corner_proper : ∀ i, cornerEq i ≠ 0 :=
    Sum.rec proper (Sum.rec (fun _ => segmentEquation_ne_zero _ _)
      (fun _ => segmentEquation_ne_zero _ _))
  obtain ⟨c, ⟨c_T, c_ball⟩, c_regular⟩ :=
    (AffineArrangement.dense_regular cornerEq corner_proper).inter_open_nonempty
      (T ∩ ball) (open_T.inter Metric.isOpen_ball) ⟨c₀, corner_T, cover (Or.inr (by simp))⟩
  obtain ⟨q_radial, initial, progress, supported, outside, outward⟩ :=
    stable a' b' q c x_in y_in q_W.1 c_T
  refine ⟨a', b', first, last, q, c, height, q_ball, q_radial, initial, progress,
    supported, outside, outward, fun i => ⟨q_regular (.inl i), c_regular (.inl i)⟩,
    fun i => ⟨avoid_x i, avoid_y i⟩, ?_,
    Q.radial_halfplane_closure_jordan q q_radial initial progress height
      (fun z hz => supported z hz) c outside outward, ?_⟩
  · intro j
    fin_cases j
    · change ∀ t i, AffineMap.lineMap y c t ≠ point i
      intro t i same
      exact avoid_y i (eq_endpoint_of_lineMap_of_segmentEquation_ne_zero
        (c_regular (.inr (.inr i))) t same).symm
    · change ∀ t i, AffineMap.lineMap c q t ≠ point i
      intro t i same
      rw [← AffineMap.lineMap_apply_one_sub] at same
      exact (ne_of_segmentEquation_ne_zero (q_regular (.inr i)))
        (eq_endpoint_of_lineMap_of_segmentEquation_ne_zero
          (c_regular (.inr (.inl i))) (1 - t) same).symm
    · change ∀ t i, AffineMap.lineMap q x t ≠ point i
      intro t i same
      rw [← AffineMap.lineMap_apply_one_sub] at same
      exact avoid_x i (eq_endpoint_of_lineMap_of_segmentEquation_ne_zero
        (q_regular (.inr i)) (1 - t) same).symm
  · have trimmed : Set.range Q.path ⊆ region := (P.trimEnds_path_subset a' b').trans on_bank
    have x_in := trimmed (Q.vertex_mem_path_range 0)
    have y_in := trimmed (Q.vertex_mem_path_range (Fin.last (n + 2)))
    have q_in : q ∈ region := Metric.ball_subset_closedBall q_W.2
    have c_in : c ∈ region := Metric.ball_subset_closedBall c_ball
    have cvx : Convex ℝ region := convex_closedBall _ _
    rintro z (on_path | ((last | middle) | first))
    · exact trimmed on_path
    · exact cvx.segment_subset y_in c_in last
    · exact cvx.segment_subset c_in q_in middle
    · exact cvx.segment_subset q_in x_in first

end Unfoldings.PolygonalChain
