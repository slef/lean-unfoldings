module

public import Unfoldings.Roof.PotentialContourPhysical
public import Unfoldings.Complex.ContourGapTerminalIndex
public import Unfoldings.Polyhedron.ContourParentBankMetric

/-! The physical ray of a source gap retains its original finite and terminal bank labels. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (F : K.PotentialCutForest f cuts)
  (contour : C.BoundaryContour (C.selectedRetain F.selection))
  (starts : C.contourOriginalVertex F.selection contour 0 ∈ F.parents.roots)
  (event : C.PositiveContourSource F.selection contour)

local notation "Length" => C.positiveContourBankLength F.selection contour event
local notation "Saved" =>
  C.processedParentRetain F.selection (C.contourFrontier F.selection contour (Fin.succ (Subtype.val event)))
local notation "Bank" => F.contourSourceBankChain contour starts event
local notation "Physical" => F.contourSourceSpatialRay contour starts event
local notation "Source" => C.positiveContourVertex F.selection contour event
local notation "space" => fun v => K.folding.toSpace Set.univ (C.vertexPoint Set.univ v)

/-- Each finite spatial vertex of the saved bank is the literal original parent iterate. -/
theorem contourSourceSpatialRay_vertex (i : Fin (Length + 2)) :
    (Physical).chain.vertex i = space (F.parents.parent^[i.val] Source) := by
  change (K.folding.boundarySpatialChain Bank).vertex i = _
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have terminal : C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex Saved (C.boundaryTurn Saved (Bank).last)) = F.parents.root Source :=
      (F.exists_contourSourceBankChain contour starts event).choose_spec.2.1
    rw [K.folding.boundarySpatialChain_vertex_last, K.folding.boundaryPosition_original_vertex,
      terminal, Fin.val_last, ← C.positiveContourBank_span F.selection contour event,
      F.parents.iterate_distanceToRoot_eq_root]
  · rw [K.folding.boundarySpatialChain_vertex_castSucc, K.folding.boundaryPosition_original_vertex,
      F.contourSourceBankChain_original contour starts event, Fin.val_castSucc]

/-- A saved gap and the final cut use the same physical affine point at
the original named finite edge, on either side of that cut. -/
theorem contourSourceSpatialRay_point_contourParent
    (v : C.Vertex Set.univ) (nonroot : v ∉ F.parents.roots)
    (member : event ∈ C.contourEdgeGapStack F.selection contour v)
    (side : Bool) (t : unitInterval) :
    (Physical).chain.point (C.contourGapBankIndex F.selection contour v nonroot event member) t =
    K.folding.toSpace F.retain
      (C.directedBoundaryPath (C.contourParentBank F.selection contour F.boundary_roots
        starts v nonroot side) t) := by
  let i := C.contourGapBankIndex F.selection contour v nonroot event member
  have original := C.contourGapBankIndex_original F.selection contour v nonroot event member
  have at_first : (Physical).chain.vertex i.castSucc = space v := by
    rw [F.contourSourceSpatialRay_vertex contour starts event, Fin.val_castSucc]
    exact congrArg space original
  have at_last : (Physical).chain.vertex i.succ = space (F.parents.parent v) := by
    rw [F.contourSourceSpatialRay_vertex contour starts event, Fin.val_succ,
      Function.iterate_succ_apply', original]
  change (Physical).chain.point i t = _
  rw [PolygonalChain.point, at_first, at_last]
  exact (K.folding.contourParentBank_position F.selection contour F.boundary_roots starts
    v nonroot side t).symm

/-- The spatial tail starts at the terminal parent and follows the
same full spatial chord vector as its final named finite edge. -/
theorem contourSourceSpatialRay_tail_eq_terminalParent
    (e : C.ContourTerminalEdge F.selection)
    (member : event ∈ C.contourEdgeGapStack F.selection contour e.val)
    (t : ℝ≥0) :
    (Physical).tail t =
      space (F.parents.parent e.val) + t.val • (space (F.parents.parent e.val) - space e.val) := by
  have first : (Physical).chain.vertex (Fin.last Length).castSucc = space e.val := by
    rw [F.contourSourceSpatialRay_vertex contour starts event, Fin.val_castSucc, Fin.val_last,
      C.contourGap_last_child F.selection contour e event member]
  have last : (Physical).chain.vertex (Fin.last (Length + 1)) = space (F.parents.parent e.val) := by
    rw [F.contourSourceSpatialRay_vertex contour starts event, Fin.val_last,
      ← C.positiveContourBank_span F.selection contour event, F.parents.iterate_distanceToRoot_eq_root,
      C.contourGap_terminal_root F.selection contour e event member]
  change (Physical).chain.vertex (Fin.last (Length + 1)) +
    t.val • ((Physical).chain.vertex (Fin.last Length).succ -
      (Physical).chain.vertex (Fin.last Length).castSucc) = _
  rw [Fin.succ_last, first, last]

end Unfoldings.ConvexRoof.PotentialCutForest
