module

public import Unfoldings.Geometry.RadialWedgeClosure
public import Unfoldings.Geometry.AffineArrangement

/-!
# Generic radial sources inside a pointed wedge

Positive radial progress is stable under a small source perturbation. Moving
slightly backward into the wedge first gives strict supporting inequalities;
density then avoids any prescribed finite family of affine lines.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

def strictRadialSources : Set Plane :=
  {q | ∀ i : Fin n, P.edge i ≠ 0 → 0 < inner ℝ (P.vertex i.castSucc - q) (P.edge i)}

theorem isOpen_strictRadialSources : IsOpen P.strictRadialSources := by
  unfold strictRadialSources
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  by_cases nonzero : P.edge i ≠ 0
  · have same : {q : Plane | P.edge i ≠ 0 →
        0 < inner ℝ (P.vertex i.castSucc - q) (P.edge i)} =
        {q : Plane | 0 < inner ℝ (P.vertex i.castSucc - q) (P.edge i)} :=
      Set.ext (fun _ => ⟨fun h => h nonzero, fun h _ => h⟩)
    rw [same]
    exact isOpen_lt continuous_const (by fun_prop)
  · simp only [nonzero, false_implies, Set.ofPred_true]
    exact isOpen_univ

theorem radialFrom_of_strictRadialSource {q : Plane} (member : q ∈ P.strictRadialSources) :
    P.RadialFrom q 0 := by
  intro i _
  apply (monotone_dist_lineMap_iff _ _ _).mpr
  change 0 ≤ inner ℝ (P.vertex i.castSucc - q) (P.edge i)
  by_cases nonzero : P.edge i ≠ 0
  · exact (member i nonzero).le
  · simp only [not_not] at nonzero
    simp only [nonzero, inner_zero_right, le_refl]

/-- A positive actual radial margin supplies the strict tests needed for generic perturbation. -/
theorem strictRadialSource_of_margin {source : Plane} {γ : ℝ} (positive : 0 < γ)
    (radial : P.RadialFrom source 0) (initial : 0 < dist source (P.vertex 0))
    (margin : ∀ i : Fin n, γ * (‖P.vertex i.castSucc - source‖ * ‖P.edge i‖) ≤
      inner ℝ (P.vertex i.castSucc - source) (P.edge i)) : source ∈ P.strictRadialSources := by
  intro i nonzero
  have radius : 0 < dist source (P.vertex i.castSucc) :=
    initial.trans_le (radial.dist_vertices_le P 0 i.castSucc le_rfl (by
      change (0 : ℕ) ≤ i.val
      omega))
  have norm_positive : 0 < ‖P.vertex i.castSucc - source‖ := by
    simpa only [dist_eq_norm'] using radius
  exact (mul_pos positive (mul_pos norm_positive (norm_pos_iff.mpr nonzero))).trans_le (margin i)

/-- Arbitrarily close generic sources preserve actual radial progress and make the wedge strict. -/
theorem exists_generic_radial_source {ι : Type*} [Finite ι] (source : Plane)
    (strict : source ∈ P.strictRadialSources)
    (initial : 0 < dist source (P.vertex 0))
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n)))
    (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane)
    (inside : ∀ j, 0 ≤ (frame.symm (P.vertex j - source)).1 ∧
      0 ≤ (frame.symm (P.vertex j - source)).2)
    (equation : ι → Plane →ᵃ[ℝ] ℝ) (proper : ∀ i, equation i ≠ 0)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ q : Plane, dist q source < δ ∧ P.RadialFrom q 0 ∧
      0 < dist q (P.vertex 0) ∧
      dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) ∧
      (∀ j, 0 < (frame.symm (P.vertex j - q)).1 ∧
        0 < (frame.symm (P.vertex j - q)).2) ∧ (∀ i, equation i q ≠ 0) := by
  let U : Set Plane := Metric.ball source δ ∩ P.strictRadialSources ∩
    {q | 0 < dist q (P.vertex 0) ∧
      dist q (P.vertex 0) < dist q (P.vertex (Fin.last n))}
  have open_initial : IsOpen {q : Plane | 0 < dist q (P.vertex 0)} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have open_progress : IsOpen {q : Plane |
      dist q (P.vertex 0) < dist q (P.vertex (Fin.last n))} :=
    isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  have open_U : IsOpen U :=
    (Metric.isOpen_ball.inter P.isOpen_strictRadialSources).inter (open_initial.inter open_progress)
  have source_U : source ∈ U := ⟨⟨Metric.mem_ball_self positive, strict⟩, initial, progress⟩
  have continuous_shift : Continuous (fun t : ℝ => source - t • frame (1, 1)) := by fun_prop
  have near : ∀ᶠ t : ℝ in nhds 0, source - t • frame (1, 1) ∈ U := by
    apply continuous_shift.continuousAt.eventually
    change U ∈ nhds (source - (0 : ℝ) • frame (1, 1))
    simpa only [zero_smul, sub_zero] using open_U.mem_nhds source_U
  obtain ⟨r, radius, bound⟩ := Metric.eventually_nhds_iff.mp near
  let ε : ℝ := r / 2
  have epsilon : 0 < ε := by dsimp [ε]; positivity
  have in_U : source - ε • frame (1, 1) ∈ U := by
    apply bound
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos epsilon]
    dsimp [ε]
    linarith
  let W : Set Plane := {q | ∀ j : Fin (n + 1),
    0 < (frame.symm (P.vertex j - q)).1 ∧ 0 < (frame.symm (P.vertex j - q)).2}
  have open_W : IsOpen W := by
    simp only [W, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro j
    have continuous_frame : Continuous frame.symm :=
      frame.symm.toLinearMap.continuous_of_finiteDimensional
    exact (isOpen_lt continuous_const
      ((continuous_frame.comp (continuous_const.sub continuous_id)).fst)).inter
      (isOpen_lt continuous_const
        ((continuous_frame.comp (continuous_const.sub continuous_id)).snd))
  have shifted_W : source - ε • frame (1, 1) ∈ W := by
    intro j
    have coordinates : P.vertex j - (source - ε • frame (1, 1)) =
        (P.vertex j - source) + ε • frame (1, 1) := by module
    rw [coordinates, map_add, map_smul, frame.symm_apply_apply]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one]
    constructor <;> linarith [(inside j).1, (inside j).2]
  obtain ⟨q, member, regular⟩ :=
    (AffineArrangement.dense_regular equation proper).inter_open_nonempty
    (U ∩ W) (open_U.inter open_W) ⟨source - ε • frame (1, 1), in_U, shifted_W⟩
  exact ⟨q, member.1.1.1, P.radialFrom_of_strictRadialSource member.1.1.2,
    member.1.2.1, member.1.2.2, member.2, regular⟩

end Unfoldings.PolygonalChain
