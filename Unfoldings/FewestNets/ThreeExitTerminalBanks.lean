module

public import Unfoldings.FewestNets.ThreeExitTerminalGerms
public import Unfoldings.Geometry.SpatialEnvelopeCutBankLift
public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCopies
public import Unfoldings.Geometry.SpatialEnvelopeHalfspaceChart
public import Unfoldings.Metric.PlacedBallComposition

/-! The two full three-exit banks retain their actual spatial metric and their sources. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.WholeCutModel

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

private theorem edist_exit (r : Root) (s t : ℝ≥0) :
    edist (SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) s.val))
      (SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)) =
        (‖R.physicalRayDirection r‖₊ : ℝ≥0∞) * edist s t := by
  have difference :
      SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) s.val) -
        SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val) =
        (s.val - t.val) • R.physicalRayDirection r := by
    rw [R.physical_point_ray M r s.property, R.physical_point_ray M r t.property,
      add_sub_add_left_eq_sub, sub_smul]
  change _ = _ * edist s.val t.val
  rw [edist_dist, dist_eq_norm, difference, norm_smul, Real.norm_eq_abs, edist_dist,
    Real.dist_eq, ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ofReal_norm, enorm_eq_nnnorm]

set_option maxHeartbeats 1100000 in
-- All metric copies refer to one fixed partition, including both ray endpoints.
/-- Both closed banks lift to the actual whole embedded forest cut. They keep
their original spatial speed and have distinct copies at every positive time. -/
theorem exists_exit_banks_with_charts (r : Root) :
    ∃ (bank : Bool → ℝ≥0 →ᵈ W.Cut) (anchor : Bool → W.Index),
      (∀ side t, (W.partition.restoreCut R.wholeCarrier (bank side t)).val =
        SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)) ∧
      (∀ side s t, edist (bank side s) (bank side t) =
        (‖R.physicalRayDirection r‖₊ : ℝ≥0∞) * edist s t) ∧
      (∀ side other : Bool, side ≠ other → ∀ s t, 0 < s.val → bank side s ≠ bank other t) ∧
      ∀ side (t : ℝ≥0), 0 < t.val → ∃ δ > 0,
        ∃ a : W.partition.faceSideHalfspace (anchor side) (orientMap (p r.val) (q r)) (W.exitSigns r),
          a.val = (M.plane (W.partition.support (anchor side))).project.symm
            (R.exits.ray (R.exitRoot r) t.val) ∧
          ∃ chart : Metric.eball (bank side t) (ENNReal.ofReal δ) ≃ᵢ Metric.ball a δ,
            ∀ y, (M.plane (W.partition.support (anchor side))).place (chart y).val.val =
              (W.partition.restoreCut R.wholeCarrier y.val).val := by
  classical
  obtain ⟨anchor, _, _, sides, _, active, face⟩ := W.exists_exit_local_model r
  let f := orientMap (p r.val) (q r)
  have proper : f ≠ 0 := orientMap_ne_zero (R.exit_endpoints_ne r)
  let single := MetricGluing.rayCut (p r.val) (q r)
  have closed : IsClosed single := MetricGluing.isClosed_rayCut _ _
  have level : ∀ x ∈ single, f x = 0 := MetricGluing.rayCut_on_line _ _
  have included : single ⊆ R.wholeCarrier := by
    intro x member
    exact Set.mem_iUnion.mpr ⟨r.val, (R.wholeCutPiece_root_eq_rayCut r).symm ▸ member⟩
  let source (side : Bool) (t : ℝ≥0) : PolygonalPoint
      ((M.plane (W.partition.support (anchor side))).project.symm ''
        W.partition.faceSideRegion (anchor side) f (W.exitSigns r)) :=
    ⟨(M.plane (W.partition.support (anchor side))).project.symm (R.exits.ray (R.exitRoot r) t.val),
      ⟨R.exits.ray (R.exitRoot r) t.val, ⟨(AffineEnvelope.mem_cell_iff _ _ _).mpr
        (active side t.val t.property), by
          change 0 ≤ AffineArrangement.signed f (W.exitSigns r (anchor side))
            (R.exits.ray (R.exitRoot r) t.val)
          rw [R.exit_ray_lineMap r t.val, AffineArrangement.signed_apply]
          have zero : f (AffineMap.lineMap (p r.val) (q r) t.val) = 0 := by
            simpa only [f, orientMap_apply] using orient_lineMap (p r.val) (q r) t.val
          rw [zero]
          simp only [neg_zero, ite_self, le_refl]⟩, rfl⟩⟩
  let place (side : Bool) := W.partition.faceSideRegionMap (anchor side) f proper (W.exitSigns r)
    (W.exit_aligned r) single closed level
  have rigid (side : Bool) : Isometry (place side) :=
    W.partition.faceSideRegionMap_isometry (anchor side) f proper (W.exitSigns r)
      (W.exit_aligned r) single closed level
  have restores (side : Bool) (t : ℝ≥0) :
      (W.partition.restoreCut single (place side (source side t))).val =
        SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val) := by
    dsimp only [place]
    rw [W.partition.restoreCut_faceSideRegionMap]
    exact (SpatialEnvelope.point_eq_place M.plane (W.partition.support (anchor side))
      (active side t.val t.property)).symm
  have metric (side : Bool) (s t : ℝ≥0) :
      edist (place side (source side s)) (place side (source side t)) =
        (‖R.physicalRayDirection r‖₊ : ℝ≥0∞) * edist s t := by
    have convex := (W.partition.convex_faceSideRegion (anchor side) f (W.exitSigns r)).affine_image
      (M.plane (W.partition.support (anchor side))).project.symm.toAffineMap
    calc
      _ = edist (source side s) (source side t) := (rigid side).edist_eq _ _
      _ = edist (source side s).val (source side t).val := PolygonalPoint.edist_eq_of_segment
        (convex.segment_subset (source side s).property (source side t).property)
      _ = edist (SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) s.val))
          (SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)) := by
        rw [SpatialEnvelope.point_eq_place M.plane (W.partition.support (anchor side))
          (active side s.val s.property),
          SpatialEnvelope.point_eq_place M.plane (W.partition.support (anchor side))
          (active side t.val t.property), (M.plane (W.partition.support (anchor side))).place.isometry.edist_eq]
      _ = _ := edist_exit (M := M) r s t
  let oneRay (side : Bool) : ℝ≥0 →ᵈ W.partition.Cut single :=
    ⟨fun t => place side (source side t), ‖R.physicalRayDirection r‖₊,
      nnnorm_ne_zero_iff.mpr (R.physicalRayDirection_ne_zero r), metric side⟩
  have horizontal (side : Bool) (t : ℝ≥0) :
      Cap.horizontal (W.partition.restoreCut single (oneRay side t)).val =
        R.exits.ray (R.exitRoot r) t.val :=
    (congrArg Cap.horizontal (restores side t)).trans (SpatialEnvelope.horizontal_point M.plane _)
  have lifted (side : Bool) : ∃ bank : ℝ≥0 →ᵈ W.Cut,
      (∀ t, W.partition.forgetCut R.wholeCarrier single included (bank t) = oneRay side t) ∧
      ∀ s t, edist (bank s) (bank t) = edist (oneRay side s) (oneRay side t) := by
    apply W.partition.exists_closedBank_lift included (oneRay side)
    intro t positive
    rw [horizontal side t]
    exact R.exists_exit_rayCut_germ r positive
  choose bank agrees bank_metric using lifted
  have restore_bank (side : Bool) (t : ℝ≥0) :
      (W.partition.restoreCut R.wholeCarrier (bank side t)).val =
        SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val) := by
    have restored := W.partition.restoreCut_forgetCut R.wholeCarrier single included (bank side t)
    rw [agrees side t] at restored
    exact (congrArg PolygonalPoint.val restored).symm.trans (restores side t)
  refine ⟨bank, anchor, restore_bank, fun side s t => (bank_metric side s t).trans (metric side s t), ?_, ?_⟩
  · intro side other different s t positive equal
    have one_equal : oneRay side s = oneRay other t := by
      rw [← agrees side s, ← agrees other t, equal]
    have separated : place side (source side s) ≠ place other (source other t) := by
      apply W.partition.faceSideRegionMap_ne_of_opposite_sign f proper (W.exitSigns r)
        (W.exit_aligned r) single closed level (anchor side) (anchor other) _ _
        (isOpen_rayForwardHalfspace (p r.val) (q r))
      · intro z forward zero
        obtain ⟨u, upos, expression⟩ := exists_positive_ray_parameter (R.exit_endpoints_ne r)
          forward zero
        exact ⟨⟨u, upos.le⟩, expression.symm⟩
      · change Cap.horizontal (W.partition.restoreCut single (oneRay side s)).val ∈ _
        rw [horizontal, R.exit_ray_lineMap r s.val]
        exact lineMap_mem_rayForwardHalfspace (R.exit_endpoints_ne r) positive
      · simpa only [sides] using different
    exact separated one_equal

  · intro side t positive
    let Q := M.plane (W.partition.support (anchor side))
    let x := R.exits.ray (R.exitRoot r) t.val
    let F := W.partition.forgetCut R.wholeCarrier single included
    have position : Cap.horizontal (W.partition.restoreCut R.wholeCarrier (bank side t)).val = x :=
      (congrArg Cap.horizontal (restore_bank side t)).trans (SpatialEnvelope.horizontal_point _ _)
    have source_x : Cap.horizontal (Q.place (source side t).val) = x :=
      ((Q.horizontal_place _).trans (Q.project.apply_symm_apply _))
    obtain ⟨ε, εpos, germ⟩ := R.exists_exit_rayCut_germ r positive
    obtain ⟨ρ, ρpos, transfer, agrees_transfer⟩ := W.partition.exists_forgetCut_ball_chart_at included
      (bank side t) εpos (fun z near => germ z (by rwa [position] at near))
    obtain ⟨δ, δpos, local_face⟩ := face side t.val positive
    have one_chart :
        ∃ σ > 0, ∃ a : W.partition.faceSideHalfspace (anchor side) f (W.exitSigns r),
          a.val = (source side t).val ∧
          ∃ chart : Metric.eball (oneRay side t) (ENNReal.ofReal σ) ≃ᵢ Metric.ball a σ,
            ∀ y, Q.place (chart y).val.val = (W.partition.restoreCut single y.val).val := by
      apply W.partition.exists_faceSideHalfspace_ball_chart (anchor side) f proper (W.exitSigns r)
        (W.exit_aligned r) single closed level (source side t)
        (isOpen_rayForwardHalfspace (p r.val) (q r))
      · intro z forward zero
        obtain ⟨s, spos, expression⟩ := exists_positive_ray_parameter (R.exit_endpoints_ne r)
          forward zero
        exact ⟨⟨s, spos.le⟩, expression.symm⟩
      · rw [source_x]
        dsimp only [x]
        rw [R.exit_ray_lineMap r t.val]
        exact lineMap_mem_rayForwardHalfspace (R.exit_endpoints_ne r) positive
      · exact δpos
      · intro z near on_side
        exact (local_face z (by rwa [source_x] at near)).2 (by rwa [sides side] at on_side)
    obtain ⟨σ, σpos, a, coordinates, model, agrees_model⟩ := one_chart
    let physical (z : W.partition.faceSideHalfspace (anchor side) f (W.exitSigns r)) : Space :=
      Q.place z.val
    have injective : Function.Injective physical :=
      fun u v same => Subtype.ext (Q.place.injective same)
    have center : physical a = (W.partition.restoreCut single (oneRay side t)).val := by
      change Q.place a.val = (W.partition.restoreCut single (place side (source side t))).val
      rw [coordinates, restores side t]
      exact (SpatialEnvelope.point_eq_place M.plane (W.partition.support (anchor side))
        (active side t.val t.property)).symm
    obtain ⟨r, rpos, chart, charts⟩ := exists_composed_placed_ball_chart F
      (fun z => (W.partition.restoreCut R.wholeCarrier z).val)
      (fun z => (W.partition.restoreCut single z).val) physical injective (agrees side t)
      (fun z => congrArg PolygonalPoint.val
        (W.partition.restoreCut_forgetCut R.wholeCarrier single included z))
      ρpos σpos transfer agrees_transfer model agrees_model center
    exact ⟨r, rpos, a, coordinates, chart, charts⟩

/-- Both original closed banks have exactly the spatial exit metric and
remain distinct at every positive parameter. -/
theorem exists_exit_banks (r : Root) :
    ∃ bank : Bool → ℝ≥0 →ᵈ W.Cut,
      (∀ side t, (W.partition.restoreCut R.wholeCarrier (bank side t)).val =
        SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)) ∧
      (∀ side s t, edist (bank side s) (bank side t) =
        (‖R.physicalRayDirection r‖₊ : ℝ≥0∞) * edist s t) ∧
      ∀ side other : Bool, side ≠ other → ∀ s t, 0 < s.val → bank side s ≠ bank other t := by
  obtain ⟨bank, _, restore, metric, apart, _⟩ := W.exists_exit_banks_with_charts r
  exact ⟨bank, restore, metric, apart⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.WholeCutModel
