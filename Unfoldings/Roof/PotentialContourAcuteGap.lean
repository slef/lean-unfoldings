module

public import Unfoldings.Roof.PotentialContourGap
public import Unfoldings.Geometry.AcuteBankCone

/-! An actual contour gap needs only a common acute cone on its saved bank. -/

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

/-- A saved bank in a common acute cone and its positive source rotation
produce the precise gap and strict radial bends used by the complete graft. -/
theorem contourSource_gap_of_acuteCone {center : ℝ}
    (curvature : C.totalInteriorAngularDefect Set.univ < π)
    (cone : (R.contourSourceRay Q starts event).InAcuteCone center) :
    OrientedBankGap (R.contourSourceRay Q starts event) (R.contourSourceOpenedRay Q starts event) ∧
      ∀ k : Fin Length,
        let bank := R.contourSourceRay Q starts event
        0 < inner ℝ (bank.chain.vertex k.succ.castSucc - bank.start) (bank.chain.edge k.succ) := by
  let chain := R.contourSourceBankChain Q starts event
  let bank := R.contourSourceRay Q starts event
  have genuine (i : Fin (Length + 1)) : bank.chain.edge i ≠ 0 :=
    C.boundaryChainRoll_edge_ne_zero chain i
  have outward := cone.outward bank
  have ray_ne : bank.direction ≠ 0 := genuine (Fin.last Length)
  have defect_le : Defect ≤ C.totalInteriorAngularDefect Set.univ := by
    simpa only [Finset.sum_singleton] using K.sum_interiorAngularDefect_le_totalCurvature {Source}
  refine ⟨bank.orientedGap_rotateSuffix_zero outward ray_ne event.property.2
    (defect_le.trans_lt curvature), ?_⟩
  intro k
  let i := k.succ
  have radii := bank.chain.vertex_radius_strictMono_of_radial bank.start outward.1 genuine
  have later : (0 : Fin (Length + 2)) < i.castSucc := by
    change 0 < k.val + 1
    omega
  have not_start : bank.chain.vertex i.castSucc - bank.start ≠ 0 := by
    intro equal
    have positions : bank.chain.vertex i.castSucc = bank.chain.vertex 0 := sub_eq_zero.mp equal
    have radii_lt := radii later
    change dist bank.start (bank.chain.vertex 0) <
      dist bank.start (bank.chain.vertex i.castSucc) at radii_lt
    rw [positions] at radii_lt
    exact (lt_irrefl _ radii_lt)
  have member : bank.chain.vertex i.castSucc ∈ bank.carrier :=
    Or.inl (bank.chain.vertex_mem_path_range i.castSucc)
  exact acuteBankCone.inner_pos (cone.displacement_mem bank member) (cone.1 i)
    not_start (genuine i)

end Unfoldings.ConvexRoof.PotentialCutForest
