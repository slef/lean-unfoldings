module

public import Unfoldings.FewestNets.ThreeExitFiniteMarks
public import Unfoldings.FewestNets.ThreeExitContourTails
public import Unfoldings.FewestNets.ThreeExitTerminalBanks
public import Unfoldings.Complex.ContourGapTerminalIndex
public import Unfoldings.Metric.ConnectedBankMatching
public import Unfoldings.Metric.PositiveClosedInterval

/-! The completed marks continue the two actual finite banks across the artificial rim. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

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

local instance terminalMarksIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

local notation "MarkAt[" h "," c "," s "," e "]" =>
  L.contourParentMark h c s (Subtype.val e) (And.left (Subtype.property e))
local notation "restore" =>
  SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier

set_option maxHeartbeats 1700000 in
-- The finite marks and the global charts come from the same physical partition.
/-- Both original contour-side labels extend to their actual whole-ray banks.
The normalized tail parameter retains the physical speed of the final finite edge. -/
theorem exists_contourTerminalBanks
    (higher : ∀ v : V, (G).height (pointOf v) < level)
    (contour : (D[higher]).BoundaryContour (F[higher]).retain)
    (starts : (D[higher]).contourOriginalVertex Sel[higher] contour 0 ∈ (F[higher]).parents.roots)
    (edge : (D[higher]).ContourTerminalEdge Sel[higher]) :
    ∃ (r : Root) (first : ℝ) (nonnegative : 0 ≤ first),
      let τ := R.exits.timeAtLevel level (R.exitRoot r)
      ∃ (before : first < τ) (bank : Bool → ℝ≥0 →ᵈ L.whole.Cut) (side : Bool → Bool),
        Function.Injective side ∧
        (∀ flag s t, edist (bank flag s) (bank flag t) =
          (‖R.physicalRayDirection r‖₊ : ℝ≥0∞) * edist s t) ∧
        (∀ flag other : Bool, flag ≠ other → ∀ s t, 0 < s.val →
          bank flag s ≠ bank other t) ∧
        (∀ flag t, (restore (bank (side flag) t)).val =
          SpatialEnvelope.point M.plane (R.exits.ray (R.exitRoot r) t.val)) ∧
        (∀ flag, ∀ t : unitInterval, MarkAt[higher,contour,starts,edge] flag t =
          bank (side flag) (nonnegativeIntervalLineMap first τ nonnegative before.le t)) := by
  obtain ⟨r, first, nonnegative, before, at_first, at_last⟩ :=
    R.exists_exit_of_fineMesh_terminalParent level M higher edge.val edge.property.1 edge.property.2
  let τ := R.exits.timeAtLevel level (R.exitRoot r)
  let time := nonnegativeIntervalLineMap first τ nonnegative before.le
  have trace (flag : Bool) (t : unitInterval) :
      Cap.horizontal (restore (MarkAt[higher,contour,starts,edge] flag t)).val = R.exits.ray (R.exitRoot r) (time t).val := by
    rw [L.horizontal_contourParentMark higher contour starts edge.val edge.property.1, at_first,
      at_last, SlopeEnvelope.ExteriorPlan.pointAtLevel]
    simp only [SlopeEnvelope.ExteriorPlan.ray, AffineMap.lineMap_apply_module']
    change _ = R.exits.point (R.exitRoot r) + (first + t.val * (τ - first)) •
      R.exits.direction (R.exits.slope (R.exitRoot r))
    module
  have pos (t : unitInterval) (u : 0 < t.val) : 0 < (time t).val :=
    add_pos_of_nonneg_of_pos nonnegative (mul_pos u (sub_pos.mpr before))
  obtain ⟨bank, _, restores, metric, separated, exhaust, _⟩ := L.whole.exists_exit_banks_with_charts r
  have assign (flag : Bool) : ∃ side : Bool, ∀ t : unitInterval, MarkAt[higher,contour,starts,edge] flag t = bank side (time t) :=
    MetricGluing.exists_bank_side_of_dense_positive bank separated (MarkAt[higher,contour,starts,edge] flag)
      (L.continuous_contourParentMark higher contour starts edge.val edge.property.1 flag) time
      (continuous_nonnegativeIntervalLineMap _ _ _ _) {t | 0 < t.val}
      (isPreconnected_positiveIcc 1) (dense_positiveIcc (by norm_num)) pos
      (fun t ht => exhaust (time t) (pos t ht) (MarkAt[higher,contour,starts,edge] flag t) (trace flag t))
  choose side agrees using assign
  have distinct : side false ≠ side true := by
    let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have bounds : 0 < t ∧ t < 1 := by
      change (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
      norm_num
    have below : (time t).val < τ := by
      change first + (1 / 2) * (τ - first) < τ
      linarith only [before]
    have τ_pos : 0 < τ := nonnegative.trans_lt before
    have height := R.exits.pointAtLevel_height level (R.exitRoot r) (R.exit_origin_below level higher r)
    rw [SlopeEnvelope.ExteriorPlan.pointAtLevel, R.exits.height_ray _ τ_pos.le] at height
    have inside : (G).height (Cap.horizontal (restore (MarkAt[higher,contour,starts,edge] false t)).val) < level := by
      rw [trace, R.exits.height_ray _ (time t).property]
      have compared := add_lt_add_right (mul_lt_mul_of_pos_right below
        (R.exits.positive (R.exitRoot r))) ((G).height (R.exits.point (R.exitRoot r)))
      exact compared.trans_eq height
    intro equal
    exact L.contourParentMark_ne_of_inside higher contour starts edge.val edge.property.1 t bounds
      inside ((agrees false t).trans (equal ▸ (agrees true t).symm))
  have injective : Function.Injective side := by
    intro a b same
    cases a <;> cases b
    · rfl
    · exact (distinct same).elim
    · exact (distinct same.symm).elim
    · rfl
  exact ⟨r, first, nonnegative, before, bank, side, injective, metric, separated,
    fun flag => restores (side flag), agrees⟩

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
