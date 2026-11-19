module

public import Unfoldings.Roof.CompatibleTerminalChartCoordinates
public import Unfoldings.Geometry.AffineBankHalfPlaneFrame
public import Unfoldings.Metric.BallIsometry

/-! Normalized forward arclength charts for whole roof terminal banks. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

open MetricGluing

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance terminalNormalizedChartIndexFintype : Fintype W.Index := W.finiteIndex


/-- At any positive time on a whole terminal bank, either occupied half-plane
gives a centered chart preserving forward physical arclength. -/
theorem exists_wholeTerminalBank_normalized_chart (r : {v // v ∈ R.parents.roots})
    (side occupied : Bool) (t : ℝ≥0) (positive : 0 < t.val) :
    ∃ ε, Nonempty (BankHalfPlaneChart
      (K.wholeTerminalBank compact nonempty R no_boundary W r side) t occupied
      (fun s : ℝ≥0 => (s.val - t.val) * ‖R.exterior.spatialDirection (R.terminalIndex r)‖) ε) := by
  let i := R.terminalIndex r
  let B := W.terminalSupportCells r
  let j := W.partition.support (B.anchor side)
  let Q := M.plane j
  let f := orientMap (R.exterior.point i) (R.exterior.ray i 1)
  let sign := W.terminalSigns r (B.anchor side)
  let h := (AffineArrangement.signed f sign).comp Q.project.toAffineMap
  let bank := K.wholeTerminalBank compact nonempty R no_boundary W r side
  let p := Q.project.symm (R.exterior.ray i t.val)
  let q := Q.project.symm (R.exterior.ray i (t.val + 1))
  have proper : h ≠ 0 := by
    have hf : f ≠ 0 := orientMap_ne_zero (R.exterior.ray_endpoints_ne i)
    have signed : AffineArrangement.signed f sign ≠ 0 := by
      cases hs : sign <;> simpa only [hs, AffineArrangement.signed, Bool.false_eq_true,
        ↓reduceIte, neg_ne_zero] using hf
    intro zero
    apply signed
    ext x
    have z := congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g (Q.project.symm x)) zero
    change AffineArrangement.signed f sign (Q.project (Q.project.symm x)) = 0 at z
    change _ = (0 : ℝ)
    simpa only [Q.project.apply_symm_apply] using z
  have on_line (s : ℝ) : h (Q.project.symm (R.exterior.ray i s)) = 0 := by
    change AffineArrangement.signed f sign (Q.project (Q.project.symm (R.exterior.ray i s))) = 0
    rw [Q.project.apply_symm_apply, AffineArrangement.signed_apply]
    have z : f (R.exterior.ray i s) = 0 := by
      dsimp only [f]
      rw [← R.exterior.ray_lineMap i s, orientMap_apply, orient_lineMap]
    rw [z, neg_zero, ite_self]
  have ray_line (s : ℝ) : AffineMap.lineMap p q s =
      Q.project.symm (R.exterior.ray i (t.val + s)) := by
    apply Q.project.injective
    change Q.project.toAffineMap (AffineMap.lineMap p q s) = _
    rw [Q.project.toAffineMap.apply_lineMap]
    simp only [p, q, AffineEquiv.coe_toAffineMap, Q.project.apply_symm_apply,
      AffineMap.lineMap_apply_module',
      SlopeEnvelope.ExteriorPlan.ray]
    rw [add_sub_add_left_eq_sub, ← sub_smul, add_sub_cancel_left, one_smul, add_smul]
    abel
  have place (s : ℝ) (nonnegative : 0 ≤ s) :
      Q.place (Q.project.symm (R.exterior.ray i s)) =
        SpatialEnvelope.point M.plane (R.exterior.ray i s) :=
    (SpatialEnvelope.point_eq_place M.plane j
      (R.exterior.terminal_cell_support_active M W.partition i
        (B.anchor side) B.threshold (B.tail side) s nonnegative)).symm
  have speed : ‖q - p‖ = ‖R.exterior.spatialDirection i‖ := by
    rw [← dist_eq_norm, ← Q.place.isometry.dist_eq, dist_eq_norm,
      place (t.val + 1) (by positivity), place t.val t.property,
      R.exterior.spatial_ray_sub M i (by positivity) t.property, add_sub_cancel_left, one_smul]
  have different : p ≠ q := by
    intro equal
    exact (norm_pos_iff.mpr (R.exterior.spatialDirection_ne_zero i)).ne'
      (speed.symm.trans (by rw [equal, sub_self, norm_zero]))
  obtain ⟨F, parameter, membership⟩ := exists_affineBankHalfPlaneFrame p q different h proper
    (on_line _) (on_line _) occupied
  obtain ⟨ε, εpos, model, model_eq, A, _, coordinates⟩ :=
    K.exists_wholeTerminalBank_chart_with_bank_coordinates compact nonempty R no_boundary W r
      side t positive
  let E := setIsometryEquiv F.toIsometryEquiv _ _ membership
  have model_center : E model = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change F model.val = 0
    have center : model.val = p := model_eq
    have named := parameter 0
    rw [AffineMap.lineMap_apply_zero, zero_mul, Complex.ofReal_zero] at named
    exact (congrArg F center).trans named
  refine ⟨ε, ⟨⟨εpos, (A.trans (metricBallEBallEquiv model ε)).trans
    (basedEBallIsometry E model _ model_center (ENNReal.ofReal ε)), ?_, ?_⟩⟩⟩
  · change E (A _).val = _
    have center : (A ⟨bank t, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr εpos)⟩).val =
        model := by
      apply Subtype.ext
      exact (coordinates t (by simp [εpos])).trans model_eq.symm
    exact (congrArg E center).trans model_center
  · intro s near
    change F (A _).val.val = _
    have relative : s.val = t.val + (s.val - t.val) := by ring
    rw [coordinates s near]
    conv_lhs => rw [relative, ← ray_line, parameter, speed]

end Unfoldings.ConvexRoof
