module

public import Unfoldings.Geometry.GenericRadialSource

/-! A bank may begin at its source: arbitrarily close sources make its first radial test strict. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane (n + 1))

/-- Move behind the first genuine edge, while retaining every later strict radial test and
any prescribed open condition at the original source. -/
theorem exists_near_sourceStart_strict
    (first : P.edge 0 ≠ 0)
    (future : ∀ i : Fin (n + 1), i ≠ 0 → P.edge i ≠ 0 →
      0 < inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i))
    {U : Set Plane} (open_U : IsOpen U) (inside : P.vertex 0 ∈ U)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ q : Plane, dist q (P.vertex 0) < δ ∧ q ∈ P.strictRadialSources ∧ q ∈ U := by
  classical
  let V : Set Plane := {q | ∀ i : Fin (n + 1), i ≠ 0 ∧ P.edge i ≠ 0 →
    0 < inner ℝ (P.vertex i.castSucc - q) (P.edge i)}
  have open_V : IsOpen V := by
    dsimp only [V]
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    by_cases active : i ≠ 0 ∧ P.edge i ≠ 0
    · have same : {q : Plane | i ≠ 0 ∧ P.edge i ≠ 0 →
          0 < inner ℝ (P.vertex i.castSucc - q) (P.edge i)} =
          {q : Plane | 0 < inner ℝ (P.vertex i.castSucc - q) (P.edge i)} :=
        Set.ext (fun _ => ⟨fun h => h active, fun h _ => h⟩)
      rw [same]
      exact isOpen_lt continuous_const (by fun_prop)
    · simp only [active, false_implies, Set.ofPred_true]
      exact isOpen_univ
  let W := V ∩ U ∩ Metric.ball (P.vertex 0) δ
  have open_W : IsOpen W := (open_V.inter open_U).inter Metric.isOpen_ball
  have at_source : P.vertex 0 ∈ W :=
    ⟨⟨fun i active => future i active.1 active.2, inside⟩, Metric.mem_ball_self positive⟩
  let move (t : ℝ) := P.vertex 0 - t • P.edge 0
  have continuous : ContinuousAt move 0 := by fun_prop
  have near : ∀ᶠ t in 𝓝 (0 : ℝ), move t ∈ W := by
    apply continuous.eventually
    change W ∈ nhds (move 0)
    simpa only [move, zero_smul, sub_zero] using open_W.mem_nhds at_source
  obtain ⟨ε, eps_positive, good⟩ := Metric.eventually_nhds_iff.mp near
  have moved := good (show dist (ε / 2) (0 : ℝ) < ε by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos eps_positive)]
    linarith)
  refine ⟨move (ε / 2), moved.2, ?_, moved.1.2⟩
  intro i nonzero
  by_cases initial : i = 0
  · subst i
    have vector : P.vertex (0 : Fin (n + 1)).castSucc - move (ε / 2) =
        (ε / 2) • P.edge 0 := by
      change P.vertex 0 - (P.vertex 0 - (ε / 2) • P.edge 0) = _
      abel
    rw [vector, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact mul_pos (half_pos eps_positive) (pow_pos (norm_pos_iff.mpr first) 2)
  · exact moved.1.1 i ⟨initial, nonzero⟩

/-- A positive margin suffices even when the first bank vertex is the source itself. -/
theorem exists_near_sourceStart_strict_of_margin {γ : ℝ} (gamma_positive : 0 < γ)
    (radial : P.RadialFrom (P.vertex 0) 0) (first : P.edge 0 ≠ 0)
    (margin : ∀ i : Fin (n + 1), γ *
      (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i))
    {U : Set Plane} (open_U : IsOpen U) (inside : P.vertex 0 ∈ U)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ q : Plane, dist q (P.vertex 0) < δ ∧ q ∈ P.strictRadialSources ∧ q ∈ U := by
  apply P.exists_near_sourceStart_strict first _ open_U inside positive
  intro i later nonzero
  have positive_index : 0 < i.val := by
    by_contra zero
    exact later (Fin.ext (by change i.val = 0; omega))
  have first_radius : 0 < dist (P.vertex 0) (P.vertex (0 : Fin (n + 1)).succ) := by
    rw [dist_eq_norm']
    change 0 < ‖P.edge 0‖
    exact norm_pos_iff.mpr first
  have lower := radial.dist_vertices_le P (0 : Fin (n + 1)).succ i.castSucc (Fin.zero_le _)
    (by change 1 ≤ i.val; omega)
  have radius : 0 < ‖P.vertex i.castSucc - P.vertex 0‖ := by
    simpa only [dist_eq_norm'] using first_radius.trans_le lower
  exact (mul_pos gamma_positive (mul_pos radius (norm_pos_iff.mpr nonzero))).trans_le (margin i)

/-- Every vertex after the genuine first edge is different from the original source. -/
theorem sourceStart_vertex_ne_zero (radial : P.RadialFrom (P.vertex 0) 0)
    (first : P.edge 0 ≠ 0) (j : Fin (n + 2)) (later : 0 < j.val) :
    P.vertex j - P.vertex 0 ≠ 0 := by
  have first_radius : 0 < dist (P.vertex 0) (P.vertex (0 : Fin (n + 1)).succ) := by
    rw [dist_eq_norm']
    change 0 < ‖P.edge 0‖
    exact norm_pos_iff.mpr first
  have lower := radial.dist_vertices_le P (0 : Fin (n + 1)).succ j (Fin.zero_le _)
    (by change 1 ≤ j.val; omega)
  have radius : 0 < ‖P.vertex j - P.vertex 0‖ := by
    simpa only [dist_eq_norm'] using first_radius.trans_le lower
  exact norm_pos_iff.mp radius

/-- Small strict-source perturbations preserve any strict scalar comparison continuous at source. -/
theorem exists_near_sourceStart_strict_with_bound {γ : ℝ} (gamma_positive : 0 < γ)
    (radial : P.RadialFrom (P.vertex 0) 0) (first : P.edge 0 ≠ 0)
    (margin : ∀ i : Fin (n + 1), γ *
      (‖P.vertex i.castSucc - P.vertex 0‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - P.vertex 0) (P.edge i))
    (f : Plane → ℝ) (continuous : ContinuousAt f (P.vertex 0)) {c : ℝ}
    (short : f (P.vertex 0) < c) {δ : ℝ} (positive : 0 < δ) :
    ∃ q : Plane, dist q (P.vertex 0) < δ ∧ q ∈ P.strictRadialSources ∧
      0 < dist q (P.vertex 0) ∧ f q < c := by
  have near : ∀ᶠ q in 𝓝 (P.vertex 0), f q < c :=
    continuous.eventually (gt_mem_nhds short)
  change {q | f q < c} ∈ nhds (P.vertex 0) at near
  obtain ⟨U, subset, open_U, inside⟩ := mem_nhds_iff.mp near
  obtain ⟨q, close, strict, in_U⟩ := P.exists_near_sourceStart_strict_of_margin
    gamma_positive radial first margin open_U inside positive
  refine ⟨q, close, strict, ?_, subset in_U⟩
  apply dist_pos.mpr
  intro equal
  have progress := strict 0 first
  rw [equal] at progress
  change 0 < inner ℝ (P.vertex 0 - P.vertex 0) (P.edge 0) at progress
  rw [sub_self, inner_zero_left] at progress
  exact (lt_irrefl (0 : ℝ)) progress

end Unfoldings.PolygonalChain
