module

public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.BankGapParameters
public import Unfoldings.Geometry.TwoBankGapSourceChart
public import Unfoldings.Geometry.SourceSectorCoordinates
public import Unfoldings.Geometry.ChainSplit
public import Unfoldings.Geometry.OpeningSourceAngle

/-! The genuine initial edges give a physical sector chart at the original gap source. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings

/-- An occupied positive source angle below a half-turn identifies the original rotation
below one full turn, with no modular ambiguity. -/
theorem initialGapAngle_rotated_of_bounds (d : ℂ) (genuine : d ≠ 0) {θ : ℝ}
    (positive : 0 < θ) (full : θ < 2 * Real.pi)
    (occupied : initialGapAngle d (complexRotation θ d) ∈ Set.Ioo (0 : ℝ) Real.pi) :
    initialGapAngle d (complexRotation θ d) = θ ∧ θ < Real.pi := by
  have e_ne : complexRotation θ d ≠ 0 := by
    simpa only [map_zero] using (complexRotation θ).injective.ne genuine
  have phase : polarRay (initialGapAngle d (complexRotation θ d)) = polarRay θ := by
    rw [polarRay_initialGapAngle d (complexRotation θ d) genuine e_ne,
      (complexRotation θ).norm_map, complexRotation_apply]
    have norm_ne : (‖d‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr genuine)
    field_simp
  have im := congrArg Complex.im phase
  simp only [polarRay_im] at im
  have sin_pos : 0 < Real.sin θ :=
    (Real.sin_pos_of_pos_of_lt_pi occupied.1 occupied.2).trans_eq im
  have small : θ < Real.pi := by
    by_contra! high
    have nonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (show θ - 2 * Real.pi ≤ 0 by linarith)
      (show -Real.pi ≤ θ - 2 * Real.pi by linarith)
    rw [Real.sin_sub_two_pi] at nonpos
    exact (not_lt_of_ge nonpos) sin_pos
  exact ⟨initialGapAngle_rotated d genuine positive small, small⟩

end Unfoldings

namespace Unfoldings.PolygonalRay

/-- The initial finite edge is present all the way to its first original endpoint. -/
theorem initial_edge_segment_subset {n : ℕ} (B : PolygonalRay ℂ (n + 1)) :
    segment ℝ B.start (B.start + B.chain.edge 0) ⊆ B.carrier := by
  have finish : B.start + B.chain.edge 0 = B.chain.vertex (0 : Fin (n + 1)).succ := by
    change B.chain.vertex 0 +
      (B.chain.vertex (0 : Fin (n + 1)).succ - B.chain.vertex 0) = _
    abel
  rw [finish, segment_eq_image_lineMap]
  rintro _ ⟨s, bounds, rfl⟩
  exact Or.inl (B.chain.point_mem_path_range 0 (⟨s, bounds⟩ : unitInterval))

end Unfoldings.PolygonalRay

namespace Unfoldings.OrientedBankGap

variable {n : ℕ} {first second : PolygonalRay ℂ (n + 1)} (G : OrientedBankGap first second)

/-- The actual canonical model has its whole source sector of the original width and frame. -/
theorem exists_model_source_chart (first_edge : first.chain.edge 0 ≠ 0)
    (second_edge : second.chain.edge 0 ≠ 0) :
    let d := first.chain.edge 0
    let e := second.chain.edge 0
    let r := min ‖d‖ ‖e‖
    0 < r ∧ initialGapAngle d e ∈ Set.Ioo (0 : ℝ) Real.pi ∧
      ∃ A : Metric.eball (G.model.edgePoint false 0 0) (ENNReal.ofReal r) ≃ᵢ
        Metric.ball (initialGapSectorOrigin d e) r,
        ∀ y, first.start + (d / (‖d‖ : ℂ)) * (A y).val.val = y.val.val := by
  let d := first.chain.edge 0
  let e := second.chain.edge 0
  let r := min ‖d‖ ‖e‖
  have dseg := first.initial_edge_segment_subset
  have eseg := second.initial_edge_segment_subset
  have bounds := first.initialGapAngle_bounds second G.first_outward G.first_nonzero
    G.second_outward G.second_nonzero G.phase d e first_edge second_edge dseg eseg
  refine ⟨lt_min (norm_pos_iff.mpr first_edge) (norm_pos_iff.mpr second_edge), bounds, ?_⟩
  let source := first.twoBankSourcePoint second G.first_outward G.first_nonzero G.second_outward
    G.second_nonzero G.phase
  have named : (G.model.edgePoint false 0 0) = source := by
    apply PolygonalPoint.ext
    change first.chain.point 0 0 = first.start
    rw [PolygonalChain.point_zero]
    rfl
  rw [named]
  obtain ⟨A, physical⟩ := first.exists_twoBankGap_source_sector_isometry second G.first_outward
    G.first_nonzero G.second_outward G.second_nonzero G.phase d e first_edge second_edge dseg eseg
  let B := initialGapSectorBallIsometry first.start d e first_edge r
  refine ⟨A.trans B.symm, fun y => ?_⟩
  have coords : B (B.symm (A y)) = A y := B.apply_symm_apply (A y)
  exact (congrArg (fun z => z.val.val) coords).trans (physical y)

end Unfoldings.OrientedBankGap
