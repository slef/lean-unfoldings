module

public import Unfoldings.Cone.AngularClosure

/-! Complete an actual slit fan by adding one genuine geometric gap sector and closing its banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n) (κ : ℝ) (positive : 0 < κ) (small : κ < Real.pi)

/-- Retain all original sectors and append the actual complementary gap sector. -/
def appendSector : AngularFan (n + 1) where
  angle := Fin.lastCases κ A.angle
  positive i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using positive
    · simpa only [Fin.lastCases_castSucc] using A.positive j
  small i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using small
    · simpa only [Fin.lastCases_castSucc] using A.small j

@[simp] theorem appendSector_angle_castSucc (i : Fin (n + 1)) :
    (A.appendSector κ positive small).angle i.castSucc = A.angle i := by simp [appendSector]

@[simp] theorem appendSector_angle_last :
    (A.appendSector κ positive small).angle (Fin.last (n + 1)) = κ := by simp [appendSector]

theorem appendSector_heading_castSucc (i : Fin (n + 2)) :
    (A.appendSector κ positive small).heading i.castSucc = A.heading i := by
  induction i using Fin.inductionOn with
  | zero => simp
  | succ i ih =>
    rw [← Fin.succ_castSucc, heading_succ, A.heading_succ,
      A.appendSector_angle_castSucc, ih]

theorem appendSector_heading_extra :
    (A.appendSector κ positive small).heading (Fin.last (n + 1)).castSucc = A.totalAngle := by
  rw [A.appendSector_heading_castSucc, A.heading_last]

theorem appendSector_totalAngle :
    (A.appendSector κ positive small).totalAngle = A.totalAngle + κ := by
  rw [← heading_last, ← Fin.succ_last, heading_succ, A.appendSector_heading_extra,
    A.appendSector_angle_last]

/-- The original cell points retain their exact Euclidean coordinates. -/
def appendSectorOriginalCell (i : Fin (n + 1)) (x : A.Cell i) :
    (A.appendSector κ positive small).Cell i.castSucc :=
  ⟨x.val, by simpa only [A.appendSector_angle_castSucc] using x.property⟩

/-- The extra sector has its actual original positive-span coordinates. -/
def appendSectorGapCell (x : planarSector κ) :
    (A.appendSector κ positive small).Cell (Fin.last (n + 1)) :=
  ⟨x.val, by simpa only [A.appendSector_angle_last] using x.property⟩

theorem appendSector_place_original (i : Fin (n + 1)) (x : A.Cell i) :
    (A.appendSector κ positive small).place i.castSucc
      (A.appendSectorOriginalCell κ positive small i x) = A.place i x := by
  change polarRay ((A.appendSector κ positive small).heading i.castSucc.castSucc) * x.val = _
  rw [A.appendSector_heading_castSucc]
  rfl

theorem appendSector_place_gap (x : planarSector κ) :
    (A.appendSector κ positive small).place (Fin.last (n + 1))
      (A.appendSectorGapCell κ positive small x) = polarRay A.totalAngle * x.val := by
  change polarRay ((A.appendSector κ positive small).heading
    (Fin.last (n + 1)).castSucc) * x.val = _
  rw [A.appendSector_heading_extra]

/-- Adding the complementary original sector and identifying its two outer banks is planar
in the actual constructed intrinsic metric, with no local-flatness certificate as input. -/
def completedPlaneIsometryEquiv (balance : A.totalAngle + κ = 2 * Real.pi) :
    (A.appendSector κ positive small).ClosedSurface ≃ᵢ ℂ :=
  (A.appendSector κ positive small).closedPlaneIsometryEquiv
    ((A.appendSector_totalAngle κ positive small).trans balance)

@[simp] theorem completedPlane_original (balance : A.totalAngle + κ = 2 * Real.pi)
    (i : Fin (n + 1)) (x : A.Cell i) :
    A.completedPlaneIsometryEquiv κ positive small balance
      ((A.appendSector κ positive small).closeMap
        ((A.appendSector κ positive small).faceMap i.castSucc
          (A.appendSectorOriginalCell κ positive small i x))) = A.place i x := by
  exact A.appendSector_place_original κ positive small i x

@[simp] theorem completedPlane_gap (balance : A.totalAngle + κ = 2 * Real.pi)
    (x : planarSector κ) :
    A.completedPlaneIsometryEquiv κ positive small balance
      ((A.appendSector κ positive small).closeMap
        ((A.appendSector κ positive small).faceMap (Fin.last (n + 1))
          (A.appendSectorGapCell κ positive small x))) = polarRay A.totalAngle * x.val := by
  exact A.appendSector_place_gap κ positive small x

end Unfoldings.AngularFan
