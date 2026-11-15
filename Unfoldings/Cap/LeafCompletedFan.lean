module

public import Unfoldings.Cap.LeafGapSector
public import Unfoldings.Cone.AppendSector
public import Unfoldings.Cone.LinkAngles

/-! Completing the actual leaf corner by its geometric bank-gap sector gives a plane metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) {w : C.Vertex retain} {n : ℕ}

/-- The geometric source angle measured from the two actual terminal bank vectors. -/
def linkGapAngle (c : (C.linkSystem retain w).Chain n) : ℝ :=
  initialGapAngle
    (D.linkDevelopFrame c (D.germRay (C.linkTurn retain w c.last)))
    (D.linkDevelopFrame c (D.germRay c.first))

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- For an actual childless cut, append precisely the sector of its original bank vectors.
Closing the two remaining banks yields a genuine plane isometry, retaining the placement
of every original corner sector and the exact placement of the added gap sector. -/
theorem exists_childless_completed_plane (D : FacewiseDevelopment C M.retain)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ M.parents.roots)
    (childless : ∀ u ∉ M.parents.roots, M.parents.parent u ≠ vertex)
    (positive : 0 < 2 * Real.pi - C.totalAngle Set.univ vertex)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    ∃ w : C.Vertex M.retain, ∃ n, ∃ c : (C.linkSystem M.retain w).Chain n,
      C.vertexForgetCuts (Set.subset_univ M.retain) w = vertex ∧
      (∀ p, c.Visited p) ∧
      D.linkGapAngle c = 2 * Real.pi - C.totalAngle Set.univ vertex ∧
      ∃ pos : 0 < D.linkGapAngle c, ∃ small : D.linkGapAngle c < Real.pi,
      let A := C.linkAngularFan M.retain w c
      ∃ E : (A.appendSector (D.linkGapAngle c) pos small).ClosedSurface ≃ᵢ ℂ,
        (∀ i (x : A.Cell i),
          E ((A.appendSector (D.linkGapAngle c) pos small).closeMap
            ((A.appendSector (D.linkGapAngle c) pos small).faceMap i.castSucc
              (A.appendSectorOriginalCell (D.linkGapAngle c) pos small i x))) = A.place i x) ∧
        (∀ x : planarSector (D.linkGapAngle c),
          E ((A.appendSector (D.linkGapAngle c) pos small).closeMap
            ((A.appendSector (D.linkGapAngle c) pos small).faceMap (Fin.last (n + 1))
              (A.appendSectorGapCell (D.linkGapAngle c) pos small x))) =
                polarRay A.totalAngle * x.val) := by
  obtain ⟨w, n, c, original, covers, angle, balance⟩ :=
    M.exists_childless_complementary_gap_angle D vertex nonroot childless positive budget
  change D.linkGapAngle c = _ at angle
  change C.totalAngle M.retain w + D.linkGapAngle c = _ at balance
  have internal : ¬ C.IsBoundaryVertex Set.univ vertex := by
    simpa only [M.roots_eq, Set.mem_ofPred_eq] using nonroot
  have spent : D.linkGapAngle c ≤ C.totalInteriorAngularDefect Set.univ := by
    have bound := K.sum_interiorAngularDefect_le_totalCurvature {vertex}
    simpa only [angle, Finset.sum_singleton, TriangleComplex.interiorAngularDefect,
      ite_eq_right internal] using bound
  have pos : 0 < D.linkGapAngle c := angle ▸ positive
  have small : D.linkGapAngle c < Real.pi := spent.trans_lt budget
  let A := C.linkAngularFan M.retain w c
  have full : A.totalAngle + D.linkGapAngle c = 2 * Real.pi := by
    rwa [C.linkAngularFan_totalAngle M.retain w c covers]
  refine ⟨w, n, c, original, covers, angle, pos, small,
    A.completedPlaneIsometryEquiv (D.linkGapAngle c) pos small full, ?_, ?_⟩
  · exact A.completedPlane_original (D.linkGapAngle c) pos small full
  · exact A.completedPlane_gap (D.linkGapAngle c) pos small full

end Unfoldings.ConvexCap.SectorForest
