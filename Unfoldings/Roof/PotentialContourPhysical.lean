module

public import Unfoldings.Roof.PotentialContourGap

/-! A source gap has a literal spatial boundary path, with its original final ray. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (F : K.PotentialCutForest f cuts)
  (contour : C.BoundaryContour (C.selectedRetain F.selection))
  (starts : C.contourOriginalVertex F.selection contour 0 ∈ F.parents.roots)
  (event : C.PositiveContourSource F.selection contour)

local notation "Length" => C.positiveContourBankLength F.selection contour event
local notation "Bank" => F.contourSourceBankChain contour starts event

/-- This path records the original physical positions, including the true
straight continuation of its last mesh edge. -/
def contourSourceSpatialRay : PolygonalRay Space (Length + 1) :=
  (K.folding.boundarySpatialChain Bank).terminalEdgeRay

theorem contourSourceSpatialRay_edge_ne_zero (i : Fin (Length + 1)) :
    (F.contourSourceSpatialRay contour starts event).chain.edge i ≠ 0 := by
  have vector := K.folding.boundarySpatialChain_edge Bank i
  intro zero
  exact K.folding.germDirection_ne_zero _ (vector.symm.trans zero)

theorem contourSourceSpatialRay_direction_ne_zero :
    (F.contourSourceSpatialRay contour starts event).direction ≠ 0 :=
  F.contourSourceSpatialRay_edge_ne_zero contour starts event (Fin.last Length)

end Unfoldings.ConvexRoof.PotentialCutForest
