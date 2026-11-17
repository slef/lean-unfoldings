module

public import Unfoldings.Roof.CompatibleTerminalFiberBanks

/-! Restoring any subset of forest cuts preserves complete original terminal banks and their
  speed. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  {M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel} (W : R.WholeCutModel M)

local instance restoredTerminalBankIndexFintype : Fintype W.Index := W.finiteIndex

variable (cuts : Set Plane) (included : cuts ⊆ R.carrier)

/-- The original named whole bank, with the unselected forest cuts restored. -/
def restoredWholeTerminalBank (r : {v // v ∈ R.parents.roots}) (side : Bool) (t : ℝ≥0) :
    W.partition.Cut cuts :=
  W.partition.forgetCut R.carrier cuts included
    (K.wholeTerminalBank compact nonempty R no_boundary W r side t)

/-- Restoration keeps the literal original spatial point at every terminal time. -/
theorem restore_restoredWholeTerminalBank (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (t : ℝ≥0) :
    (W.partition.restoreCut cuts
      (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side t)).val =
        SpatialEnvelope.point M.plane (R.exterior.ray (R.terminalIndex r) t.val) :=
  (congrArg PolygonalPoint.val (W.partition.restoreCut_forgetCut R.carrier cuts included
    (K.wholeTerminalBank compact nonempty R no_boundary W r side t))).trans
      (K.restoreCut_wholeTerminalBank compact nonempty R no_boundary W r side t)

/-- The straight original spatial ray prevents any shortcut after cuts are restored. -/
theorem edist_restoredWholeTerminalBank (r : {v // v ∈ R.parents.roots}) (side : Bool)
    (s t : ℝ≥0) :
    edist (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side s)
      (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side t) =
        (‖R.exterior.spatialDirection (R.terminalIndex r)‖₊ : ℝ≥0∞) * edist s t := by
  apply le_antisymm
  · exact (W.partition.forgetCut_lipschitz R.carrier cuts included
      (K.wholeTerminalBank compact nonempty R no_boundary W r side s)
      (K.wholeTerminalBank compact nonempty R no_boundary W r side t)).trans_eq
        ((one_mul _).trans
          (K.edist_wholeTerminalBank compact nonempty R no_boundary W r side s t))
  · have lower := (PolygonalPoint.ambient_edist_le_distance
      (W.partition.restoreCut cuts
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side s))
      (W.partition.restoreCut cuts
        (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side
          t))).trans
      ((W.partition.restoreCut_lipschitz cuts _ _).trans_eq (one_mul _))
    rw [K.restore_restoredWholeTerminalBank, K.restore_restoredWholeTerminalBank] at lower
    exact (R.exterior.edist_spatial_ray M (R.terminalIndex r) s.property t.property).symm.trans_le
      lower

/-- Every partially restored original terminal bank is an entire closed half-line dilation. -/
def restoredWholeTerminalBankDilation (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    ℝ≥0 →ᵈ W.partition.Cut cuts where
  toFun := K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side
  edist_eq' := ⟨‖R.exterior.spatialDirection (R.terminalIndex r)‖₊,
    nnnorm_ne_zero_iff.mpr (R.exterior.spatialDirection_ne_zero (R.terminalIndex r)),
    K.edist_restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side⟩

/-- The full restored bank is a closed embedded half-line, including its original source. -/
theorem restoredWholeTerminalBank_isClosedEmbedding (r : {v // v ∈ R.parents.roots}) (side : Bool) :
    Topology.IsClosedEmbedding
      (K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side) :=
  Dilation.isClosedEmbedding
    (K.restoredWholeTerminalBankDilation compact nonempty R no_boundary W cuts included r side)

/-- Every positive terminal copy in any partial forest cut comes from one of the named
original whole banks. The sides may coincide after cuts are restored. -/
theorem exists_restoredWholeTerminalBank_side (r : {v // v ∈ R.parents.roots})
    (t : ℝ≥0) (positive : 0 < t.val) (x : W.partition.Cut cuts)
    (position : Cap.horizontal (W.partition.restoreCut cuts x).val =
      R.exterior.ray (R.terminalIndex r) t.val) :
    ∃ side : Bool,
      x = K.restoredWholeTerminalBank compact nonempty R no_boundary W cuts included r side t := by
  obtain ⟨y, at_x⟩ := W.partition.forgetCut_surjective R.carrier cuts included x
  have restored := (congrArg (fun p => Cap.horizontal p.val)
    (W.partition.restoreCut_forgetCut R.carrier cuts included y)).symm
  have original : Cap.horizontal (W.partition.restoreCut R.carrier y).val =
      R.exterior.ray (R.terminalIndex r) t.val := by
    exact restored.trans ((congrArg (fun z => Cap.horizontal
      (W.partition.restoreCut cuts z).val) at_x).trans position)
  obtain ⟨side, same, _⟩ := K.existsUnique_wholeTerminalBank_side compact nonempty R no_boundary W
    r t positive y original
  exact ⟨side, at_x.symm.trans (congrArg (W.partition.forgetCut R.carrier cuts included) same)⟩

end Unfoldings.ConvexRoof
