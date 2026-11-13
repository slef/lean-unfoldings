module

public import Unfoldings.Roof.CompletionDomain

public import Unfoldings.Roof.CompletionSectorQuadrants
public import Unfoldings.Roof.CompletionOriginalPlacementAgreement
public import Unfoldings.Roof.CompletionOriginalForestRetention
public import Unfoldings.Roof.SectorQuadrants

/-!
Construct actual common quadrant frames on original faces using their physical cap completion.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

/-- The uniform frame is chosen from the actual auxiliary development, then transferred by
whole-face isometric agreement. No original horizontal rim or calibration witness is assumed. -/
theorem exists_uniform_original_sectorFrameData (t : ℝ) (positive : 0 < t) (small : t < 1) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C),
        K.TiltBound φ → ∀ {origin : Plane} (M : K.SectorForest t origin),
          ∀ D : FacewiseDevelopment C M.retain, Nonempty (M.SectorFrameData positive small D) := by
  classical
  obtain ⟨φ, bounds, normal, control⟩ :=
    exists_uniform_completion_fiveSectorFrameData.{u, v} t positive small
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt origin M D
  obtain ⟨T⟩ := K.exists_completionMesh bounds.1 bounds.2
    (show IsCompact (∅ : Set Plane) from isCompact_empty)
    K.originalEdgeEquations K.originalEdgeEquations_ne_zero
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest T positive small).val
  have height (i) : (3 : ℝ) / 4 ≤
      (T.supportPlanes i).normal 2 :=
    normal.trans (K.completionPlanes_tilt bounds.1 bounds.2 tilt T.tentHeight i)
  obtain ⟨E, _local_isometry⟩ := M.completionOutward_exists_development T positive small height
  let : PreconnectedSpace (Metric.closedBall (0 : Plane) 1) :=
    Subtype.preconnectedSpace (convex_closedBall (0 : Plane) 1).isPreconnected
  let : PreconnectedSpace (C.Realization M.retain) :=
    M.cutDisk.symm.surjective.denseRange.preconnectedSpace M.cutDisk.symm.continuous
  obtain ⟨A, agree⟩ := L.originalPart.exists_development_agreeing_original_placements
    M.retain R.retain E (M.completionOriginalRetain_subset_radial T R) D
  obtain ⟨_budget, frames⟩ := control K tilt M T
  obtain ⟨B⟩ := frames (R.completedDevelopment A)
  let := @Fintype.ofFinite _ L.originalPart.partition.finite
  let frame := R.calibratedFrame (R.completedDevelopment A) B.anchor B.reference
  have direction_eq (i : L.originalPart.originalPieceSet) (direction : Plane) :
      (R.completedDevelopment A).developedDirection L.cap i.val direction =
        D.roofDirection K (L.originalPart.originalParent i) direction := by
    have charts : A.projectedPlacement L.cap i.val =
        D.roofPlacement K (L.originalPart.originalParent i) := AffineEquiv.ext (agree i)
    exact congrArg (fun chart : Plane ≃ᵃ[ℝ] Plane => chart.linear direction) charts
  have fine_face (f : Face) : ∃ i : L.originalPart.originalPieceSet,
      L.originalPart.originalParent i = f := by
    obtain ⟨i, parent, _⟩ := L.originalPart.original_piece_cover f
      ((K.projectedTriangle f).vertex 0) ((K.projectedTriangle f).vertex_mem 0)
    exact ⟨i, parent⟩
  refine ⟨{ frame := frame, projection_positive := ?_, quadrants := ?_ }⟩
  · intro f a b area
    obtain ⟨i, parent⟩ := fine_face f
    have result := R.calibratedFrame_positive (R.completedDevelopment A) B.anchor B.reference
      i.val a b area
    change 0 < (starRingEnd ℂ (frame
      ((R.completedDevelopment A).developedDirection L.cap i.val a)) *
      frame ((R.completedDevelopment A).developedDirection L.cap i.val b)).im at result
    rw [direction_eq i a, direction_eq i b, parent] at result
    exact result
  · intro i f direction inside nonzero
    obtain ⟨j, parent⟩ := fine_face f
    have result := B.quadrants (Sum.inl i) j.val direction
      (inDirectionWedge_of_closedThreeSector positive.le small i inside) nonzero
    change 0 < ((Complex.orthonormalBasisOneI.repr.trans
      (threeSectorFrame t positive small i).place)
        (frame ((R.completedDevelopment A).developedDirection L.cap j.val direction))).re ∧
      0 < ((Complex.orthonormalBasisOneI.repr.trans
        (threeSectorFrame t positive small i).place)
          (frame ((R.completedDevelopment A).developedDirection L.cap j.val
            direction))).im at result
    rw [direction_eq j direction, parent] at result
    exact result

end Unfoldings.ConvexRoof
