module

public import Unfoldings.Cone.AttachSectorPlane
public import Unfoldings.Geometry.SourceSectorCoordinates
public import Unfoldings.Metric.Reparametrize

/-! Attach the genuine geometric source sector to the two banks of the retained intrinsic fan. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) (source d e : ℂ) (genuine : d ≠ 0)

/-- The second piece uses its actual physical sector coordinates. -/
def physicalCompletionCell : Bool → Type
  | false => A.Surface
  | true => initialGapSector source d e

instance physicalCompletionCell_emetric (i : Bool) :
    EMetricSpace (A.physicalCompletionCell source d e i) := by
  cases i <;> dsimp [physicalCompletionCell] <;> infer_instance

/-- Rigidly straighten only the added geometric sector; keep the original metric fan. -/
def physicalCompletionCoordinates (i : Bool) : A.physicalCompletionCell source d e i ≃ᵢ
    A.completionCell (initialGapAngle d e) i :=
  match i with
  | false => IsometryEquiv.refl _
  | true => (initialGapSectorIsometryEquiv source d e genuine).symm

/-- The old last bank attaches to the actual first gap bank, and the other gap bank
attaches to the old first bank, at equal intrinsic radii. -/
def physicalCompletionGlue :=
  MetricGluing.reparametrizeGlue (A.physicalCompletionCoordinates source d e genuine)
    (A.completionGlue (initialGapAngle d e))

abbrev PhysicalCompleted := MetricGluing.Realization (A.physicalCompletionCell source d e)
  (A.physicalCompletionGlue source d e genuine)

def physicalCompletedOriginal : A.Surface → A.PhysicalCompleted source d e genuine :=
  MetricGluing.of (A.physicalCompletionCell source d e)
    (A.physicalCompletionGlue source d e genuine) false

def physicalCompletedGap : initialGapSector source d e → A.PhysicalCompleted source d e genuine :=
  MetricGluing.of (A.physicalCompletionCell source d e)
    (A.physicalCompletionGlue source d e genuine) true

/-- The original first geometric bank is attached, not an arbitrary sector side. -/
theorem physicalCompletion_first_bank (r : ℝ≥0) :
    A.physicalCompletedOriginal source d e genuine
      (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
    A.physicalCompletedGap source d e genuine
      (initialGapSectorIsometryEquiv source d e genuine (gapStart (initialGapAngle d e) r)) := by
  apply MetricGluing.point_eq_of_glue
  refine ⟨r, Or.inl ⟨rfl, ?_⟩⟩
  dsimp only [physicalCompletionCoordinates]
  congr 1
  exact (initialGapSectorIsometryEquiv source d e genuine).symm_apply_apply _

/-- The old first bank receives the actual second geometric gap bank. -/
theorem physicalCompletion_second_bank (r : ℝ≥0) :
    A.physicalCompletedGap source d e genuine
      (initialGapSectorIsometryEquiv source d e genuine (gapFinish (initialGapAngle d e) r)) =
    A.physicalCompletedOriginal source d e genuine (A.faceMap 0 (A.start 0 r)) := by
  apply MetricGluing.point_eq_of_glue
  refine ⟨r, Or.inr ⟨?_, rfl⟩⟩
  dsimp only [physicalCompletionCoordinates]
  congr 1
  exact (initialGapSectorIsometryEquiv source d e genuine).symm_apply_apply _

/-- The attached first gap bank is the exact original unit edge ray. -/
theorem physicalGap_first_bank_value (r : ℝ≥0) :
    (initialGapSectorIsometryEquiv source d e genuine (gapStart (initialGapAngle d e) r)).val =
      source + (d / (‖d‖ : ℂ)) * (r : ℂ) := rfl

/-- The attached second gap bank is the other exact original unit edge ray. -/
theorem physicalGap_second_bank_value (other : e ≠ 0) (r : ℝ≥0) :
    (initialGapSectorIsometryEquiv source d e genuine (gapFinish (initialGapAngle d e) r)).val =
      source + (e / (‖e‖ : ℂ)) * (r : ℂ) := by
  rw [initialGapSectorIsometryEquiv_apply]
  change source + (d / (‖d‖ : ℂ)) * ((r : ℝ) • polarRay (initialGapAngle d e)) = _
  rw [Complex.real_smul, polarRay_initialGapAngle d e genuine other]
  have nonzero : d / (‖d‖ : ℂ) ≠ 0 := div_ne_zero genuine
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr genuine))
  have norm_d_nonzero : (‖d‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr genuine)
  congr 1
  field_simp

/-- Completing by the actual geometric sector yields the exact whole-plane metric. -/
def physicalCompletionPlaneIsometryEquiv
    (positive : 0 < initialGapAngle d e) (small : initialGapAngle d e < Real.pi)
    (balance : A.totalAngle + initialGapAngle d e = 2 * Real.pi) :
    A.PhysicalCompleted source d e genuine ≃ᵢ ℂ :=
  (MetricGluing.reparametrizeIsometryEquiv (A.physicalCompletionCoordinates source d e genuine)
    (A.completionGlue (initialGapAngle d e))).trans
      (A.completionPlaneIsometryEquiv (initialGapAngle d e) positive small balance)

@[simp] theorem physicalCompletionPlane_original
    (positive : 0 < initialGapAngle d e) (small : initialGapAngle d e < Real.pi)
    (balance : A.totalAngle + initialGapAngle d e = 2 * Real.pi) (x : A.Surface) :
    A.physicalCompletionPlaneIsometryEquiv source d e genuine positive small balance
      (A.physicalCompletedOriginal source d e genuine x) = A.develop x := rfl

@[simp] theorem physicalCompletionPlane_gap
    (positive : 0 < initialGapAngle d e) (small : initialGapAngle d e < Real.pi)
    (balance : A.totalAngle + initialGapAngle d e = 2 * Real.pi)
    (x : initialGapSector source d e) :
    A.physicalCompletionPlaneIsometryEquiv source d e genuine positive small balance
      (A.physicalCompletedGap source d e genuine x) =
        polarRay A.totalAngle * ((d / (‖d‖ : ℂ))⁻¹ * (x.val - source)) := rfl

end Unfoldings.AngularFan
