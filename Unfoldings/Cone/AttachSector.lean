module

public import Unfoldings.Cone.AppendSector

/-! A retained slit fan and one complementary gap sector, attached along their actual two banks. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) (κ : ℝ) (positive : 0 < κ) (small : κ < Real.pi)

/-- The entire retained metric fan and the separate gap sector are the two pieces. -/
def completionCell : Bool → Type
  | false => A.Surface
  | true => planarSector κ

instance completionCell_emetric (i : Bool) : EMetricSpace (A.completionCell κ i) := by
  cases i <;> dsimp [completionCell] <;> infer_instance

def gapStart (r : ℝ≥0) : planarSector κ :=
  ⟨(r : ℂ), (r : ℝ), r.coe_nonneg, 0, le_rfl, by simp⟩

def gapFinish (r : ℝ≥0) : planarSector κ :=
  ⟨(r : ℝ) • polarRay κ, 0, le_rfl, (r : ℝ), r.coe_nonneg, by simp⟩

/-- The first gap bank attaches to the last original bank; the other closes to the first.
Both identifications use the original intrinsic radius. -/
def completionGlue (x y : MetricGluing.Total (A.completionCell κ)) : Prop :=
  ∃ r : ℝ≥0,
    (x = ⟨false, A.faceMap (Fin.last n) (A.finish (Fin.last n) r)⟩ ∧
      y = ⟨true, gapStart κ r⟩) ∨
    (x = ⟨true, gapFinish κ r⟩ ∧ y = ⟨false, A.faceMap 0 (A.start 0 r)⟩)

abbrev Completed := MetricGluing.Realization (A.completionCell κ) (A.completionGlue κ)

def completedOriginal : A.Surface → A.Completed κ :=
  MetricGluing.of (A.completionCell κ) (A.completionGlue κ) false

def completedGap : planarSector κ → A.Completed κ :=
  MetricGluing.of (A.completionCell κ) (A.completionGlue κ) true

theorem completedOriginal_lipschitz : LipschitzWith 1 (A.completedOriginal κ) :=
  MetricGluing.of_lipschitz _ _ _

theorem completedGap_lipschitz : LipschitzWith 1 (A.completedGap κ) :=
  MetricGluing.of_lipschitz _ _ _

/-- Regroup the original sectors into their already constructed retained fan metric. -/
def completionCellMap (i : Fin (n + 2)) : (A.appendSector κ positive small).Cell i →
    A.Completed κ :=
  Fin.lastCases
    (fun x => A.completedGap κ ⟨x.val, by simpa using x.property⟩)
    (fun j x => A.completedOriginal κ (A.faceMap j ⟨x.val, by simpa using x.property⟩)) i

@[simp] theorem completionCellMap_original (i : Fin (n + 1))
    (x : (A.appendSector κ positive small).Cell i.castSucc) :
    A.completionCellMap κ positive small i.castSucc x =
      A.completedOriginal κ (A.faceMap i ⟨x.val, by simpa using x.property⟩) := by
  simp [completionCellMap]

@[simp] theorem completionCellMap_gap
    (x : (A.appendSector κ positive small).Cell (Fin.last (n + 1))) :
    A.completionCellMap κ positive small (Fin.last (n + 1)) x =
      A.completedGap κ ⟨x.val, by simpa using x.property⟩ := by
  simp [completionCellMap]

theorem completionCellMap_lipschitz (i : Fin (n + 2)) :
    LipschitzWith 1 (A.completionCellMap κ positive small i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have cast_isometry : Isometry (fun x : (A.appendSector κ positive small).Cell
        (Fin.last (n + 1)) => (⟨x.val, by simpa using x.property⟩ : planarSector κ)) :=
      fun _ _ => rfl
    simpa only [completionCellMap, Fin.lastCases_last, one_mul, Function.comp_def] using
      (A.completedGap_lipschitz κ).comp cast_isometry.lipschitzWith
  · have cast_isometry : Isometry (fun x : (A.appendSector κ positive small).Cell j.castSucc =>
        (⟨x.val, by simpa using x.property⟩ : A.Cell j)) := fun _ _ => rfl
    simpa only [completionCellMap, Fin.lastCases_castSucc, one_mul, Function.comp_def] using
      (A.completedOriginal_lipschitz κ).comp
        ((A.faceMap_lipschitz j).comp cast_isometry.lipschitzWith)

theorem completionCellMap_compatible (x y : MetricGluing.Total
    (A.appendSector κ positive small).Cell)
    (joined : (A.appendSector κ positive small).glue x y) :
    A.completionCellMap κ positive small x.1 x.2 =
      A.completionCellMap κ positive small y.1 y.2 := by
  obtain ⟨i, r, rfl, rfl⟩ := joined
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.succ_last, completionCellMap_original, completionCellMap_gap]
    simpa only [finish, start, gapStart, appendSector_angle_castSucc,
      completedOriginal, completedGap,
      faceMap, MetricGluing.of] using
      (MetricGluing.point_eq_of_glue (A.completionCell κ)
        (glue := A.completionGlue κ) ⟨r, Or.inl ⟨rfl, rfl⟩⟩)
  · simp only [Fin.succ_castSucc, completionCellMap_original]
    apply congrArg (A.completedOriginal κ)
    simpa only [finish, start, appendSector_angle_castSucc, faceMap, MetricGluing.of] using
      (MetricGluing.point_eq_of_glue A.Cell (glue := A.glue) ⟨j, r, rfl, rfl⟩)

/-- Passing from the appended fan into the two-piece attachment uses the actual seam relation. -/
def completionFromSlit : (A.appendSector κ positive small).Surface → A.Completed κ :=
  MetricGluing.lift _ _ (A.completionCellMap κ positive small)
    (A.completionCellMap_lipschitz κ positive small)
    (A.completionCellMap_compatible κ positive small)

@[simp] theorem completionFromSlit_faceMap (i : Fin (n + 2))
    (x : (A.appendSector κ positive small).Cell i) :
    A.completionFromSlit κ positive small ((A.appendSector κ positive small).faceMap i x) =
      A.completionCellMap κ positive small i x := rfl

theorem completionFromSlit_lipschitz : LipschitzWith 1 (A.completionFromSlit κ positive small) :=
  MetricGluing.lift_lipschitz _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The remaining outer seam becomes precisely the other named gap-bank attachment. -/
def completionFromClosed : (A.appendSector κ positive small).ClosedSurface → A.Completed κ :=
  MetricGluing.lift _ _ (fun _ => A.completionFromSlit κ positive small)
    (fun _ => A.completionFromSlit_lipschitz κ positive small) (by
      rintro x y ⟨r, first, last⟩
      rw [first, last, completionFromSlit_faceMap, completionFromSlit_faceMap]
      change A.completionCellMap κ positive small (Fin.last (n + 1)) _ =
        A.completionCellMap κ positive small (0 : Fin (n + 1)).castSucc _
      rw [completionCellMap_gap, completionCellMap_original]
      simpa only [finish, start, gapFinish, appendSector_angle_last,
        completedGap, completedOriginal,
        faceMap, MetricGluing.of] using
        (MetricGluing.point_eq_of_glue (A.completionCell κ)
          (glue := A.completionGlue κ) ⟨r, Or.inr ⟨rfl, rfl⟩⟩))

@[simp] theorem completionFromClosed_closeMap (x : (A.appendSector κ positive small).Surface) :
    A.completionFromClosed κ positive small ((A.appendSector κ positive small).closeMap x) =
      A.completionFromSlit κ positive small x := rfl

theorem completionFromClosed_lipschitz :
    LipschitzWith 1 (A.completionFromClosed κ positive small) :=
  MetricGluing.lift_lipschitz _ _ _ _ _

end Unfoldings.AngularFan
