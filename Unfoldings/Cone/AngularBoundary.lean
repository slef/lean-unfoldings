module

public import Unfoldings.Cone.AngularHomeomorph

/-!
# The outer banks are exactly the boundary of the half-plane model

Both original outer-ray radius parameters are preserved, with opposite signs
on the boundary line. The boundary characterization follows by injectivity of
the constructed homeomorphism, without any restriction on total angle.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem develop_outer_finish (r : ℝ≥0) :
    A.develop (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      (r : ℝ) • polarRay A.totalAngle := by
  rw [A.develop_faceMap]
  change polarRay (A.heading (Fin.last n).castSucc) *
    ((r : ℝ) • polarRay (A.angle (Fin.last n))) = _
  calc
    _ = (r : ℝ) • polarRay (A.heading (Fin.last n).castSucc + A.angle (Fin.last n)) := by
      rw [polarRay_add]
      simp only [Complex.real_smul]
      ring
    _ = _ := by rw [← A.heading_succ, Fin.succ_last, A.heading_last]

@[simp] theorem quarterSectorHomeomorph_start (r : ℝ≥0) :
    A.quarterSectorHomeomorph (A.faceMap 0 (A.start 0 r)) =
      quadrantSectorHomeomorph (Real.pi / 2) (by simp)
        ⟨((r : ℝ), 0), by exact ⟨r.property, le_refl 0⟩⟩ := by
  apply Subtype.ext
  change A.compressedQuarter.develop
    (A.changeAngles A.compressedQuarter (A.faceMap 0 (A.start 0 r))) = _
  rw [A.changeAngles_faceMap, A.changeCell_start, A.compressedQuarter.develop_faceMap]
  simp [place, start, sectorCombination]

@[simp] theorem quarterSectorHomeomorph_finish (r : ℝ≥0) :
    A.quarterSectorHomeomorph (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      quadrantSectorHomeomorph (Real.pi / 2) (by simp)
        ⟨(0, (r : ℝ)), by exact ⟨le_refl 0, r.property⟩⟩ := by
  apply Subtype.ext
  change A.compressedQuarter.develop
    (A.changeAngles A.compressedQuarter
      (A.faceMap (Fin.last n) (A.finish (Fin.last n) r))) = _
  rw [A.changeAngles_faceMap, A.changeCell_finish, A.compressedQuarter.develop_outer_finish,
    A.compressedQuarter_totalAngle]
  simp [sectorCombination]

@[simp] theorem halfPlaneHomeomorph_start (r : ℝ≥0) :
    A.halfPlaneHomeomorph (A.faceMap 0 (A.start 0 r)) =
      ⟨((r : ℝ), 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  change sectorHalfPlaneHomeomorph _ _
    (A.quarterSectorHomeomorph (A.faceMap 0 (A.start 0 r))) = _
  rw [A.quarterSectorHomeomorph_start, sectorHalfPlaneHomeomorph_quadrant,
    PlanarTopology.quadrantHalfPlaneHomeomorph_firstRay]

@[simp] theorem halfPlaneHomeomorph_finish (r : ℝ≥0) :
    A.halfPlaneHomeomorph (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      ⟨(-(r : ℝ), 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  change sectorHalfPlaneHomeomorph _ _
    (A.quarterSectorHomeomorph (A.faceMap (Fin.last n) (A.finish (Fin.last n) r))) = _
  rw [A.quarterSectorHomeomorph_finish, sectorHalfPlaneHomeomorph_quadrant,
    PlanarTopology.quadrantHalfPlaneHomeomorph_secondRay]

def outerBanks : Set A.Surface :=
  Set.range (fun r : ℝ≥0 => A.faceMap 0 (A.start 0 r)) ∪
    Set.range (fun r : ℝ≥0 => A.faceMap (Fin.last n) (A.finish (Fin.last n) r))

theorem halfPlaneHomeomorph_boundary_iff (z : A.Surface) :
    (A.halfPlaneHomeomorph z).val.2 = 0 ↔ z ∈ A.outerBanks := by
  constructor
  · intro boundary
    by_cases nonnegative : 0 ≤ (A.halfPlaneHomeomorph z).val.1
    · left
      let r : ℝ≥0 := ⟨(A.halfPlaneHomeomorph z).val.1, nonnegative⟩
      refine ⟨r, A.halfPlaneHomeomorph.injective ?_⟩
      rw [A.halfPlaneHomeomorph_start]
      apply Subtype.ext
      exact Prod.ext rfl boundary.symm
    · right
      let r : ℝ≥0 := ⟨-(A.halfPlaneHomeomorph z).val.1, neg_nonneg.mpr (le_of_not_ge nonnegative)⟩
      refine ⟨r, A.halfPlaneHomeomorph.injective ?_⟩
      rw [A.halfPlaneHomeomorph_finish]
      apply Subtype.ext
      exact Prod.ext (neg_neg _) boundary.symm
  · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · rw [A.halfPlaneHomeomorph_start]
    · rw [A.halfPlaneHomeomorph_finish]

end Unfoldings.AngularFan
