module

public import Unfoldings.Roof.CompletionOriginalBankWindowGeometry
public import Unfoldings.Roof.CompletionChainClosure
public import Unfoldings.Geometry.RadialTraceComparison
public import Unfoldings.Geometry.ChainEndTrimPaths
public import Unfoldings.Geometry.ChainSplit

/-! Actual trimmed physical banks have exactly the geometric trimmed radial carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement.TrimmedBankWindow

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance originalBankWindowTraceIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain (n + 1)}
  {R : E.OriginalChainRefinement retain coarse} {a b : unitInterval}
  (W : R.TrimmedBankWindow a b)

open Classical in
/-- No point of the actual intrinsic window leaves the original whole projected bank. -/
theorem cap_projected_path_subset :
    Set.range (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).path ⊆
      Set.range (K.folding.projectedBoundaryChain coarse).path := by
  have geometry := E.cap.projectedBoundaryChain_interval E.originalPieceSet R.chain
    W.firstIndex.val W.length W.fits
  have fits : W.firstIndex.val + (W.length + 1) ≤ R.length + 1 := by
    have bound := W.fits
    omega
  have contained := PolygonalChain.interval_path_range_subset
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain)
    W.firstIndex.val (W.length + 1) fits
  have equal := congrArg (fun P : PolygonalChain Plane (W.length + 1) => Set.range P.path) geometry
  exact fun _ member => R.cap_projected_path_range.subset (contained (equal.subset member))

open Classical in
/-- Every exact intrinsic bank window inherits radial order from the original entire chain. -/
theorem cap_projected_radialFrom (control : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom control 0) :
    (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).RadialFrom control 0 :=
  E.cap.projectedBoundaryChain_interval_radialFrom E.originalPieceSet R.chain
    W.firstIndex.val W.length W.fits control (R.cap_projected_radialFrom control radial)

open Classical in
/-- The actual cap window is exactly the entire geometric trimmed path. The original
radial coordinate identifies every point, independently of all subdivision choices. -/
theorem cap_projected_trace_eq_trim (control : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom control 0) :
    Set.range (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).path =
      Set.range ((K.folding.projectedBoundaryChain coarse).trimEnds a b).path :=
  (K.folding.projectedBoundaryChain coarse).path_range_eq_of_radial_subsets control radial
    (by omega) (E.cap.projectedBoundaryChain E.originalPieceSet W.chain)
    ((K.folding.projectedBoundaryChain coarse).trimEnds a b)
    (W.cap_projected_radialFrom control radial)
    ((K.folding.projectedBoundaryChain coarse).trimEnds_radialFrom a b radial)
    W.cap_projected_path_subset ((K.folding.projectedBoundaryChain coarse).trimEnds_path_subset a b)
    (W.cap_projected_initial.trans
      ((K.folding.projectedBoundaryChain coarse).trimEnds_start a b).symm)
    (W.cap_projected_terminal.trans
      ((K.folding.projectedBoundaryChain coarse).trimEnds_last a b).symm)

open Classical in
/-- A comparison source may differ from the original controlling source. Its radial
geometry on the trimmed path still transfers to the actual whole physical window. -/
theorem cap_projected_radialFrom_trim (control : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom control 0) (source : Plane)
    (trim_radial : ((K.folding.projectedBoundaryChain coarse).trimEnds a b).RadialFrom source 0) :
    (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).RadialFrom source 0 := by
  intro i _ t s ordered
  have same := W.cap_projected_trace_eq_trim control radial
  apply PolygonalChain.dist_le_of_control_radius_le
    ((K.folding.projectedBoundaryChain coarse).trimEnds a b) control
      ((K.folding.projectedBoundaryChain coarse).trimEnds_radialFrom a b radial)
      (by omega) source trim_radial
  · exact same.subset (PolygonalChain.point_mem_path_range
      (E.cap.projectedBoundaryChain E.originalPieceSet W.chain) i t)
  · exact same.subset (PolygonalChain.point_mem_path_range
      (E.cap.projectedBoundaryChain E.originalPieceSet W.chain) i s)
  · exact W.cap_projected_radialFrom control radial i (Nat.zero_le _) ordered

open Classical in
/-- The whole actual comparison closure, including all three closing segments, is unchanged. -/
theorem cap_projected_closure_eq_trim (control : Plane)
    (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom control 0)
    (source closing : Plane) :
    (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).threeSegmentClosure source closing =
      ((K.folding.projectedBoundaryChain coarse).trimEnds a b).threeSegmentClosure
        source closing := by
  have first := W.cap_projected_initial.trans
    ((K.folding.projectedBoundaryChain coarse).trimEnds_start a b).symm
  have last := W.cap_projected_terminal.trans
    ((K.folding.projectedBoundaryChain coarse).trimEnds_last a b).symm
  exact congrArg₂ (fun path rest : Set Plane => path ∪ rest)
    (W.cap_projected_trace_eq_trim control radial)
    (congrArg₂ (fun finish start : Plane =>
      (segment ℝ finish closing ∪ segment ℝ closing source) ∪ segment ℝ source start) last first)

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement.TrimmedBankWindow
