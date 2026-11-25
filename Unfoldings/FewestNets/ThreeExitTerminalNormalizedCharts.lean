module

public import Unfoldings.FewestNets.ThreeExitTerminalBanks
public import Unfoldings.Geometry.AffineBankHalfPlaneFrame
public import Unfoldings.Metric.BallIsometry

/-! Normalized forward arclength charts for the actual whole three-exit banks. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.WholeCutModel

open MetricGluing

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (W : R.WholeCutModel M)

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "Root" => {r : V // r ∈ R.stems.choice.parents.roots}
local notation "p" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "q" => (fun (r : Root) => R.exits.ray (R.exitRoot r) 1)

/-- Choose both forward banks with charts preserving absolute exit arclength.
The same choice exhausts all roof copies along the exit. -/
theorem exists_exit_banks_with_normalized_charts (r : Root) :
    ∃ bank : Bool → ℝ≥0 →ᵈ W.Cut,
      (∀ side t, (W.partition.restoreCut R.wholeCarrier (bank side t)).val =
        SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)) ∧
      (∀ side s t, edist (bank side s) (bank side t) =
        (‖R.physicalRayDirection r‖₊ : ℝ≥0∞) * edist s t) ∧
      (∀ side other : Bool, side ≠ other → ∀ s t, 0 < s.val → bank side s ≠ bank other t) ∧
      (∀ (t : ℝ≥0), 0 < t.val → ∀ x : W.Cut,
        Cap.horizontal (W.partition.restoreCut R.wholeCarrier x).val =
          R.exits.ray (R.exitRoot r) t.val →
          ∃ side, x = bank side t) ∧
      ∀ side occupied (t : ℝ≥0), 0 < t.val → ∃ ε, Nonempty
        (BankHalfPlaneChart (bank side) t occupied
          (fun s : ℝ≥0 => (s.val - t.val) * ‖R.physicalRayDirection r‖) ε) := by
  obtain ⟨bank, anchor, restore, metric, apart, exhaust, placed, charts⟩ :=
    W.exists_exit_banks_with_charts r
  refine ⟨bank, restore, metric, apart, exhaust, ?_⟩
  intro side occupied t positive
  let Q := M.plane (W.partition.support (anchor side))
  let f := orientMap (p r.val) (q r)
  let sign := W.exitSigns r (anchor side)
  let h := (AffineArrangement.signed f sign).comp Q.project.toAffineMap
  let ray := R.exits.ray (R.exitRoot r)
  let x := Q.project.symm (ray t.val)
  let y := Q.project.symm (ray (t.val + 1))
  have proper : h ≠ 0 := by
    have hf : f ≠ 0 := orientMap_ne_zero (R.exit_endpoints_ne r)
    have signed : AffineArrangement.signed f sign ≠ 0 := by
      cases hs : sign <;> simpa only [hs, AffineArrangement.signed, Bool.false_eq_true,
        ↓reduceIte, neg_ne_zero] using hf
    intro zero
    apply signed
    ext z
    have value := congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g (Q.project.symm z)) zero
    change AffineArrangement.signed f sign (Q.project (Q.project.symm z)) = 0 at value
    change AffineArrangement.signed f sign z = 0
    rwa [Q.project.apply_symm_apply] at value
  have on_line (s : ℝ) : h (Q.project.symm (ray s)) = 0 := by
    change AffineArrangement.signed f sign (Q.project (Q.project.symm (ray s))) = 0
    rw [Q.project.apply_symm_apply, AffineArrangement.signed_apply]
    have zero : f (ray s) = 0 := by
      change f (R.exits.ray (R.exitRoot r) s) = 0
      rw [R.exit_ray_lineMap r s]
      simpa only [f, orientMap_apply] using orient_lineMap (p r.val) (q r) s
    rw [zero, neg_zero, ite_self]
  have ray_line (s : ℝ) : AffineMap.lineMap x y s = Q.project.symm (ray (t.val + s)) := by
    apply Q.project.injective
    change Q.project.toAffineMap (AffineMap.lineMap x y s) = _
    rw [Q.project.toAffineMap.apply_lineMap]
    simp only [x, y, ray, AffineEquiv.coe_toAffineMap, Q.project.apply_symm_apply,
      AffineMap.lineMap_apply_module', SlopeEnvelope.ExteriorPlan.ray]
    rw [add_sub_add_left_eq_sub, ← sub_smul, add_sub_cancel_left, one_smul, add_smul]
    abel
  have place (s : ℝ) (nonnegative : 0 ≤ s) : Q.place (Q.project.symm (ray s)) =
      SpatialEnvelope.point M.plane (ray s) := placed side ⟨s, nonnegative⟩
  have speed : ‖y - x‖ = ‖R.physicalRayDirection r‖ := by
    rw [← dist_eq_norm, ← Q.place.isometry.dist_eq, dist_eq_norm]
    change ‖Q.place (Q.project.symm (ray (t.val + 1))) - Q.place (Q.project.symm (ray t.val))‖ = _
    rw [place (t.val + 1) (by positivity), place t.val t.property]
    change ‖SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) (t.val + 1)) -
      SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)‖ = _
    rw [R.physical_point_ray M r (by positivity), R.physical_point_ray M r t.property,
      add_sub_add_left_eq_sub, ← sub_smul, add_sub_cancel_left, one_smul]
  have different : x ≠ y := by
    intro equal
    exact (norm_pos_iff.mpr (R.physicalRayDirection_ne_zero r)).ne'
      (speed.symm.trans (by rw [equal, sub_self, norm_zero]))
  obtain ⟨F, parameter, membership⟩ := exists_affineBankHalfPlaneFrame x y different h proper
    (on_line _) (on_line _) occupied
  obtain ⟨ε, ε_pos, model, model_eq, A, actual⟩ := charts side t positive
  have coordinates (s : ℝ≥0) (near : bank side s ∈ Metric.eball (bank side t) (ENNReal.ofReal ε)) :
      (A ⟨bank side s, near⟩).val.val = Q.project.symm (ray s.val) := by
    apply Q.place.injective
    exact (actual ⟨bank side s, near⟩).trans ((restore side s).trans (place s.val s.property).symm)
  let E := setIsometryEquiv F.toIsometryEquiv _ _ membership
  have model_center : E model = bankHalfPlaneOrigin occupied := by
    apply Subtype.ext
    change F model.val = 0
    have at_zero := parameter 0
    rw [AffineMap.lineMap_apply_zero, zero_mul, Complex.ofReal_zero] at at_zero
    exact (congrArg F model_eq).trans at_zero
  refine ⟨ε, ⟨⟨ε_pos, (A.trans (metricBallEBallEquiv model ε)).trans
    (basedEBallIsometry E model _ model_center (ENNReal.ofReal ε)), ?_, ?_⟩⟩⟩
  · change E (A _).val = _
    have center : (A ⟨bank side t, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr ε_pos)⟩).val =
        model := Subtype.ext ((coordinates t _).trans model_eq.symm)
    exact (congrArg E center).trans model_center
  · intro s near
    change F (A _).val.val = _
    have relative : s.val = t.val + (s.val - t.val) := by ring
    rw [coordinates s near]
    conv_lhs => rw [relative, ← ray_line, parameter, speed]

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.WholeCutModel
