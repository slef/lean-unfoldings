module

public import Unfoldings.Cone.AttachSector

/-! The actual two-piece complementary-sector attachment is isometric to the whole plane. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) (κ : ℝ) (positive : 0 < κ) (small : κ < Real.pi)

/-- The entire old fan keeps its development, and the gap follows its last real heading. -/
def completionPlacement : (i : Bool) → A.completionCell κ i → ℂ
  | false => A.develop
  | true => fun x => polarRay A.totalAngle * x.val

theorem completionPlacement_lipschitz (i : Bool) :
    LipschitzWith 1 (A.completionPlacement κ i) := by
  cases i
  · exact A.develop_lipschitz
  · exact ((rotation (Circle.exp A.totalAngle)).isometry.comp isometry_subtype_coe).lipschitzWith

theorem completionPlacement_compatible (balance : A.totalAngle + κ = 2 * Real.pi)
    (x y : MetricGluing.Total (A.completionCell κ)) (joined : A.completionGlue κ x y) :
    A.completionPlacement κ x.1 x.2 = A.completionPlacement κ y.1 y.2 := by
  obtain ⟨r, joined⟩ := joined
  rcases joined with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change A.develop (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      polarRay A.totalAngle * (r : ℂ)
    rw [develop_faceMap, place_finish, Fin.succ_last, heading_last, mul_comm]
  · change polarRay A.totalAngle * ((r : ℝ) • polarRay κ) =
      A.develop (A.faceMap 0 (A.start 0 r))
    rw [develop_faceMap, place_start]
    have closed : polarRay (A.totalAngle + κ) = 1 := by
      rw [balance]
      simp [polarRay]
    have zero : A.heading (0 : Fin (n + 1)).castSucc = 0 := A.heading_zero
    rw [zero, polarRay_zero, mul_one, Complex.real_smul]
    calc
      _ = (r : ℂ) * (polarRay A.totalAngle * polarRay κ) := by ring
      _ = _ := by rw [← polarRay_add, closed, mul_one]

def completionDevelop (balance : A.totalAngle + κ = 2 * Real.pi) : A.Completed κ → ℂ :=
  MetricGluing.lift _ _ (A.completionPlacement κ) (A.completionPlacement_lipschitz κ)
    (A.completionPlacement_compatible κ balance)

theorem completionDevelop_lipschitz (balance : A.totalAngle + κ = 2 * Real.pi) :
    LipschitzWith 1 (A.completionDevelop κ balance) := MetricGluing.lift_lipschitz _ _ _ _ _

@[simp] theorem completionDevelop_original (balance : A.totalAngle + κ = 2 * Real.pi)
    (x : A.Surface) : A.completionDevelop κ balance (A.completedOriginal κ x) = A.develop x := rfl

@[simp] theorem completionDevelop_gap (balance : A.totalAngle + κ = 2 * Real.pi)
    (x : planarSector κ) :
    A.completionDevelop κ balance (A.completedGap κ x) = polarRay A.totalAngle * x.val := rfl

theorem completionDevelop_cellMap (balance : A.totalAngle + κ = 2 * Real.pi)
    (i : Fin (n + 2)) (x : (A.appendSector κ positive small).Cell i) :
    A.completionDevelop κ balance (A.completionCellMap κ positive small i x) =
      (A.appendSector κ positive small).place i x := by
  revert x
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro x
    rw [completionCellMap_gap, completionDevelop_gap]
    change polarRay A.totalAngle * x.val =
      polarRay ((A.appendSector κ positive small).heading (Fin.last (n + 1)).castSucc) * x.val
    rw [appendSector_heading_extra]
  · intro x
    rw [completionCellMap_original, completionDevelop_original, develop_faceMap]
    change polarRay (A.heading j.castSucc) * x.val =
      polarRay ((A.appendSector κ positive small).heading j.castSucc.castSucc) * x.val
    rw [appendSector_heading_castSucc]

theorem completionDevelop_fromClosed (balance : A.totalAngle + κ = 2 * Real.pi)
    (x : (A.appendSector κ positive small).ClosedSurface) :
    A.completionDevelop κ balance (A.completionFromClosed κ positive small x) =
      A.completedPlaneIsometryEquiv κ positive small balance x := by
  obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective _ _ x
  cases i
  obtain ⟨⟨j, q⟩, rfl⟩ := MetricGluing.point_surjective _ _ p
  exact A.completionDevelop_cellMap κ positive small balance j q

theorem completionFromClosed_surjective :
    Function.Surjective (A.completionFromClosed κ positive small) := by
  intro x
  obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective _ _ x
  cases i
  · obtain ⟨⟨j, q⟩, rfl⟩ := MetricGluing.point_surjective _ _ p
    refine ⟨(A.appendSector κ positive small).closeMap
      ((A.appendSector κ positive small).faceMap j.castSucc
        (A.appendSectorOriginalCell κ positive small j q)), ?_⟩
    rw [completionFromClosed_closeMap, completionFromSlit_faceMap, completionCellMap_original]
    rfl
  · refine ⟨(A.appendSector κ positive small).closeMap
      ((A.appendSector κ positive small).faceMap (Fin.last (n + 1))
        (A.appendSectorGapCell κ positive small p)), ?_⟩
    rw [completionFromClosed_closeMap, completionFromSlit_faceMap, completionCellMap_gap]
    rfl

include positive small in
theorem completionDevelop_isometry (balance : A.totalAngle + κ = 2 * Real.pi) :
    Isometry (A.completionDevelop κ balance) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using A.completionDevelop_lipschitz κ balance x y
  · obtain ⟨u, rfl⟩ := A.completionFromClosed_surjective κ positive small x
    obtain ⟨v, rfl⟩ := A.completionFromClosed_surjective κ positive small y
    rw [A.completionDevelop_fromClosed, A.completionDevelop_fromClosed,
      (A.completedPlaneIsometryEquiv κ positive small balance).isometry.edist_eq]
    simpa only [ENNReal.coe_one, one_mul] using
      A.completionFromClosed_lipschitz κ positive small u v

/-- Attaching a genuine complementary sector to both named banks gives the plane metric.
The old piece retains its original fan metric, including distances across the slit. -/
def completionPlaneIsometryEquiv (balance : A.totalAngle + κ = 2 * Real.pi) :
    A.Completed κ ≃ᵢ ℂ where
  toEquiv := Equiv.ofBijective (A.completionDevelop κ balance) (by
    refine ⟨(A.completionDevelop_isometry κ positive small balance).injective, ?_⟩
    intro z
    obtain ⟨x, equal⟩ := (A.completedPlaneIsometryEquiv κ positive small balance).surjective z
    exact ⟨A.completionFromClosed κ positive small x,
      (A.completionDevelop_fromClosed κ positive small balance x).trans equal⟩)
  isometry_toFun := by
    change Isometry (A.completionDevelop κ balance)
    exact A.completionDevelop_isometry κ positive small balance

@[simp] theorem completionPlane_original (balance : A.totalAngle + κ = 2 * Real.pi)
    (x : A.Surface) :
    A.completionPlaneIsometryEquiv κ positive small balance (A.completedOriginal κ x) =
      A.develop x := rfl

@[simp] theorem completionPlane_gap (balance : A.totalAngle + κ = 2 * Real.pi)
    (x : planarSector κ) :
    A.completionPlaneIsometryEquiv κ positive small balance (A.completedGap κ x) =
      polarRay A.totalAngle * x.val := rfl

end Unfoldings.AngularFan
