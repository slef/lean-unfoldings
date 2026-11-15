module

public import Unfoldings.Cap.LeafCompletedFan
public import Unfoldings.Cone.PhysicalGapCompletion

/-! The actual leaf's geometric source sector completes its retained intrinsic corner fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) {w : C.Vertex retain} {n : ℕ}
  (c : (C.linkSystem retain w).Chain n)

def linkFirstBankVector : ℂ := D.linkDevelopFrame c (D.germRay c.first)

def linkLastBankVector : ℂ :=
  D.linkDevelopFrame c (D.germRay (C.linkTurn retain w c.last))

theorem linkLastBankVector_ne_zero : D.linkLastBankVector c ≠ 0 := by
  simpa only [linkLastBankVector, map_zero] using (D.linkDevelopFrame c).injective.ne
    (D.germRay_ne_zero (C.linkTurn retain w c.last))

/-- Use the actual two named bank vectors to orient the added geometric sector. -/
abbrev LinkGeometricCompletion (source : ℂ) :=
  (C.linkAngularFan retain w c).PhysicalCompleted source
    (D.linkLastBankVector c) (D.linkFirstBankVector c) (D.linkLastBankVector_ne_zero c)

def linkGeometricOriginal (source : ℂ) : (C.linkAngularFan retain w c).Surface →
    D.LinkGeometricCompletion c source :=
  (C.linkAngularFan retain w c).physicalCompletedOriginal source
    (D.linkLastBankVector c) (D.linkFirstBankVector c) (D.linkLastBankVector_ne_zero c)

def linkGeometricGap (source : ℂ) :
    initialGapSector source (D.linkLastBankVector c) (D.linkFirstBankVector c) →
      D.LinkGeometricCompletion c source :=
  (C.linkAngularFan retain w c).physicalCompletedGap source
    (D.linkLastBankVector c) (D.linkFirstBankVector c) (D.linkLastBankVector_ne_zero c)

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- The leaf's genuine geometric gap sector, attached to both actual terminal banks, fills its
retained metric fan to a plane. The original development and geometric gap coordinates are kept. -/
theorem exists_childless_geometric_completion (D : FacewiseDevelopment C M.retain)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (positive : 0 < 2 * Real.pi - C.totalAngle Set.univ vertex)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) (source : ℂ) :
    ∃ w : C.Vertex M.retain, ∃ n, ∃ c : (C.linkSystem M.retain w).Chain n,
      C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex ∧
      (∀ p, c.Visited p) ∧
      D.linkGapAngle c = 2 * Real.pi - C.totalAngle Set.univ vertex ∧
      ∃ E : D.LinkGeometricCompletion c source ≃ᵢ ℂ,
        (∀ x, E (D.linkGeometricOriginal c source x) =
          (C.linkAngularFan M.retain w c).develop x) ∧
        (∀ x, E (D.linkGeometricGap c source x) =
          polarRay (C.linkAngularFan M.retain w c).totalAngle *
            ((D.linkLastBankVector c / (‖D.linkLastBankVector c‖ : ℂ))⁻¹ * (x.val - source))) := by
  obtain ⟨w, n, c, original, covers, angle, pos, small, _E, _old, _gap⟩ :=
    M.exists_childless_completed_plane D vertex nonroot childless positive budget
  let A := C.linkAngularFan M.retain w c
  have balance : A.totalAngle + initialGapAngle
      (D.linkLastBankVector c) (D.linkFirstBankVector c) = 2 * Real.pi := by
    change A.totalAngle + D.linkGapAngle c = 2 * Real.pi
    rw [C.linkAngularFan_totalAngle M.retain w c covers, angle,
      M.totalAngle_at_childless_copy vertex nonroot childless w original]
    ring
  refine ⟨w, n, c, original, covers, angle,
    A.physicalCompletionPlaneIsometryEquiv source (D.linkLastBankVector c) (D.linkFirstBankVector c)
      (D.linkLastBankVector_ne_zero c) pos small balance, ?_, ?_⟩
  · exact A.physicalCompletionPlane_original source
      (D.linkLastBankVector c) (D.linkFirstBankVector c) (D.linkLastBankVector_ne_zero c)
      pos small balance
  · exact A.physicalCompletionPlane_gap source
      (D.linkLastBankVector c) (D.linkFirstBankVector c) (D.linkLastBankVector_ne_zero c)
      pos small balance

end Unfoldings.ConvexCap.SectorForest
