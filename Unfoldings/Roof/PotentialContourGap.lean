module

public import Unfoldings.Roof.PotentialContourBanks
public import Unfoldings.Roof.SharpCurvatureBudget
public import Unfoldings.Geometry.SourceOpeningBankGap
public import Unfoldings.Geometry.TerminalEdgeRay
public import Unfoldings.Geometry.PolygonalVertexRays
public import Unfoldings.Complex.BoundaryChainAperture

/-! A positive source opens a gap in its actual saved-frontier bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)
  (Q : C.BoundaryContour (C.selectedRetain R.selection))
  (starts : C.contourOriginalVertex R.selection Q 0 ∈ R.parents.roots)
  (event : C.PositiveContourSource R.selection Q)

local notation "Length" => C.positiveContourBankLength R.selection Q event
local notation "Source" => C.positiveContourVertex R.selection Q event
local notation "Defect" => C.interiorAngularDefect Set.univ Source

/-- Extend the actual saved bank along its last direction. -/
def contourSourceRay : PolygonalRay ℂ (Length + 1) :=
  (C.boundaryChainRoll (R.contourSourceBankChain Q starts event)).terminalEdgeRay

/-- Only the newly processed source contributes a rotation at the saved stage. -/
def contourSourceOpenedRay : PolygonalRay ℂ (Length + 1) :=
  (R.contourSourceRay Q starts event).rotateSuffix 0 Defect

/-- Positive radial progress produces a concrete, nondegenerate source gap at each event. -/
theorem contourSource_gap {d : ℝ} (positive : 0 < d)
    (curvature : C.totalInteriorAngularDefect Set.univ < π)
    (radial : let P := C.boundaryChainRoll (R.contourSourceBankChain Q starts event)
      ∀ (j : Fin (Length + 2)) (i : Fin (Length + 1)), j.val ≤ i.val →
        d * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
          inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i)) :
    OrientedBankGap (R.contourSourceRay Q starts event) (R.contourSourceOpenedRay Q starts event) ∧
      ∀ k : Fin Length,
        let bank := R.contourSourceRay Q starts event
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
  let chain := R.contourSourceBankChain Q starts event
  let path := C.boundaryChainRoll chain
  let first := R.contourSourceRay Q starts event
  have outward : path.Outward := fun j i before =>
    (mul_nonneg positive.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (radial j i before)
  have genuine (i : Fin (Length + 1)) : path.edge i ≠ 0 :=
    C.boundaryChainRoll_edge_ne_zero chain i
  have ray_outward : first.Outward := path.terminalEdgeRay_outward outward
  have ray_ne : first.direction ≠ 0 := genuine (Fin.last Length)
  have defect_le : Defect ≤ C.totalInteriorAngularDefect Set.univ := by
    simpa only [Finset.sum_singleton] using K.sum_interiorAngularDefect_le_totalCurvature {Source}
  refine ⟨first.orientedGap_rotateSuffix_zero ray_outward ray_ne event.property.2
    (defect_le.trans_lt curvature), ?_⟩
  intro k
  let i := k.succ
  have radial_from := (path.radiallyMonotone_iff_outward.mpr outward) 0
  have radii := path.vertex_radius_strictMono_of_radial (path.vertex 0) radial_from genuine
  have later : (0 : Fin (Length + 2)) < i.castSucc := by
    change 0 < k.val + 1
    omega
  have dist_pos : 0 < dist (path.vertex 0) (path.vertex i.castSucc) :=
    (dist_nonneg : 0 ≤ dist (path.vertex 0) (path.vertex 0)).trans_lt (radii later)
  have norm_pos : 0 < ‖path.vertex i.castSucc - path.vertex 0‖ :=
    by simpa only [dist_eq_norm'] using dist_pos
  exact (mul_pos positive (mul_pos norm_pos (norm_pos_iff.mpr (genuine i)))).trans_le
    (radial 0 i (Nat.zero_le _))

end Unfoldings.ConvexRoof.PotentialCutForest
