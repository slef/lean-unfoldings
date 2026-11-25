module

public import Unfoldings.FewestNets.ThreeExitTerminalMarks
public import Unfoldings.Metric.ForwardBankParameter

/-! Whole contour continuations keep the exact terminal join and spatial affine parameter. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))
local notation "Root" => {r : V // r ∈ R.stems.choice.parents.roots}

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance terminalContinuationIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

local notation "MarkAt[" h "," c "," s "," e "]" =>
  L.contourParentMark h c s (Subtype.val e) (And.left (Subtype.property e))
local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier

/-- A pair of normalized continuations of the original finite parent marks. -/
structure ContourTerminalContinuation
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (edge : (D[higher]).ContourTerminalEdge Sel[higher]) where
  mark : Bool → ℝ≥0 →ᵈ L.whole.Cut
  join (side : Bool) : mark side 0 = MarkAt[higher,contour,starts,edge] side 1
  position (side : Bool) (t : ℝ≥0) :
    (restore (mark side t)).val = (restore (MarkAt[higher,contour,starts,edge] side 1)).val +
      t.val • ((restore (MarkAt[higher,contour,starts,edge] side 1)).val - (restore (MarkAt[higher,contour,starts,edge] side 0)).val)
  spatial_edist (side : Bool) (s t : ℝ≥0) :
    edist (mark side s) (mark side t) = edist (restore (mark side s)).val (restore (mark side t)).val
  same_length (s t : ℝ≥0) : edist (mark false s) (mark false t) = edist (mark true s) (mark true t)
  disjoint (side other : Bool) (different : side ≠ other) (s t : ℝ≥0) :
    mark side s ≠ mark other t
  normalized_chart (side occupied : Bool) (t : ℝ≥0) :
    ∃ ε, Nonempty (BankHalfPlaneChart (mark side) t occupied
      (fun s : ℝ≥0 => (s.val - t.val) * (Dilation.ratio (mark side)).val) ε)

set_option maxHeartbeats 1400000 in
-- Both affinely parameterized tracks refer to the exact whole banks.
theorem exists_contourTerminalContinuation
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (edge : (D[higher]).ContourTerminalEdge Sel[higher]) :
    Nonempty (L.ContourTerminalContinuation higher contour starts edge) := by
  obtain ⟨r, first, nonnegative, before, bank, label, injective, metric, distinct, restores, agrees, charts⟩ :=
    L.exists_contourTerminalBanks higher contour starts edge
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  have τ_pos : 0 < τ := nonnegative.trans_lt before
  let start : ℝ≥0 := ⟨τ, τ_pos.le⟩
  let advance : ℝ≥0 := ⟨τ - first, (sub_pos.mpr before).le⟩
  have advance_ne : advance ≠ 0 := fun zero =>
    (sub_pos.mpr before).ne' (congrArg Subtype.val zero)
  let time := forwardBankParameter start advance
  let speed := ‖R.physicalRayDirection r‖₊ * advance
  have speed_ne : speed ≠ 0 :=
    mul_ne_zero (nnnorm_ne_zero_iff.mpr (R.physicalRayDirection_ne_zero r)) advance_ne
  let normalized (side : Bool) (t : ℝ≥0) := bank (label side) (time t)
  have norm_metric (side : Bool) (s t : ℝ≥0) :
      edist (normalized side s) (normalized side t) = (speed : ℝ≥0∞) * edist s t := by
    change edist (bank (label side) (forwardBankParameter start advance s))
      (bank (label side) (forwardBankParameter start advance t)) = _
    rw [metric, edist_forwardBankParameter, ← mul_assoc]
    simp only [speed, ENNReal.coe_mul]
  let mark (side : Bool) : ℝ≥0 →ᵈ L.whole.Cut :=
    ⟨normalized side, speed, speed_ne, norm_metric side⟩
  have at_zero : nonnegativeIntervalLineMap first τ nonnegative before.le 0 = ⟨first, nonnegative⟩ :=
    Subtype.ext (by simp [nonnegativeIntervalLineMap])
  have at_one : nonnegativeIntervalLineMap first τ nonnegative before.le 1 = start :=
    Subtype.ext (by simp [nonnegativeIntervalLineMap, start])
  refine ⟨⟨mark, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro side
    have h := agrees side 1
    rw [at_one] at h
    change bank (label side) (forwardBankParameter start advance 0) = MarkAt[higher,contour,starts,edge] side 1
    rw [forwardBankParameter_zero]
    exact h.symm
  · intro side t
    have finite_start := agrees side 0
    have finite_end := agrees side 1
    rw [at_zero] at finite_start
    rw [at_one] at finite_end
    change (restore (bank (label side) (time t))).val = _
    rw [finite_start, finite_end, restores side (time t), restores side start,
      restores side ⟨first, nonnegative⟩]
    have positive : 0 ≤ (time t).val := (time t).property
    rw [R.physical_point_ray M r positive, R.physical_point_ray M r τ_pos.le,
      R.physical_point_ray M r nonnegative]
    change _ + (τ + (τ - first) * t.val) • R.physicalRayDirection r = _
    module
  · intro side s t
    change edist (bank (label side) (time s)) (bank (label side) (time t)) =
      edist (restore (bank (label side) (time s))).val (restore (bank (label side) (time t))).val
    rw [restores side (time s), restores side (time t), WholeCutModel.edist_exit (M := M), metric]
  · intro s t
    exact (norm_metric false s t).trans (norm_metric true s t).symm
  · intro side other different s t
    have positive : 0 < (time s).val :=
      add_pos_of_pos_of_nonneg τ_pos (mul_nonneg advance.property s.property)
    exact distinct (label side) (label other) (fun same => different (injective same))
      (time s) (time t) positive

  · intro side occupied t
    have ray_positive : 0 < (time t).val :=
      add_pos_of_pos_of_nonneg τ_pos (mul_nonneg advance.property t.property)
    obtain ⟨ε, ⟨chart⟩⟩ := charts (label side) occupied (time t) ray_positive
    refine ⟨ε, ⟨⟨chart.positive, chart.chart, chart.centered, ?_⟩⟩⟩
    intro s near
    refine (chart.parameter (time s) near).trans (congrArg Complex.ofReal ?_)
    have ratio : Dilation.ratio (mark side) = speed :=
      (Dilation.ratio_unique (f := mark side) (x := (0 : ℝ≥0)) (y := 1)
        (by simp) (edist_ne_top _ _) (norm_metric side 0 1)).symm
    rw [ratio]
    change ((τ + (τ - first) * s.val) - (τ + (τ - first) * t.val)) * ‖R.physicalRayDirection r‖ =
      (s.val - t.val) * (‖R.physicalRayDirection r‖ * (τ - first))
    ring

/-- The full original tail data, chosen with its proved finite join. -/
def contourTerminalContinuation
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (edge : (D[higher]).ContourTerminalEdge Sel[higher]) : L.ContourTerminalContinuation higher contour starts edge :=
  Classical.choice (L.exists_contourTerminalContinuation higher contour starts edge)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
