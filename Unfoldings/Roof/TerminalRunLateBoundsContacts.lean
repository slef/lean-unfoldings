module

public import Unfoldings.Roof.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.PositiveWidthBankStartOrder
public import Unfoldings.Cap.RegularCircleRadius
public import Unfoldings.Cap.RadialStripCircleWidth
public import Unfoldings.Geometry.StripBankContacts
public import Unfoldings.Topology.FiniteRecordProgress

/-! Late surviving circle crossings progress beyond an actual terminal of a finite collapsed run. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outerDomain : Set Plane} {F : K.SkirtTailFamily outerDomain (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}

variable
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = outerDomain) {cutoff : ℝ}
    (deep : Metric.closedBall (origin) cutoff ⊆ interior (outerDomain))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision) {ε : ℝ}
    (traces : ∀ cell : {S : MonotoneStrip // S ∈ P.cells},
      R.RadialStripTraceData positive small D
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i cell.val ε cutoff)
    (curvature_covered : ∀ v : FineC.Vertex Set.univ,
      0 < FineC.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.extendedGeometricCuts F)
    (budget : FineC.totalInteriorAngularDefect Set.univ < Real.pi)
    (nonnegative : 0 ≤ ε) (small_error : ε ≤ 1 / 2)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement Q
        (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (pinches : ∀ cell : {S : MonotoneStrip // S ∈ P.cells}, cell.val.ApproachedPinchesIn
      (Set.range (fun v : {v : FineC.Vertex Set.univ // Q.projectedVertex v ∈
          M.extendedGeometricCuts F} =>
        (fiveSectorFrame t positive small i).place
          (Q.projectedVertex v.val - origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.BankCircleSlice (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)

include outward footprint deep curvature_covered budget contacts tails radius_positive far

/-- All intervening collapsed banks are identified with the selected terminal's
actual parent path at the late crossing height. -/
theorem late_upper_circle_im_ge_run_terminal_of_contacts (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (late : (terminals pivot).height ≤ slice.upperHeight) :
    ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).im ≤
      ((traces source).value (source.val.upper.point slice.upperHeight)).im := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨j, s, _, tracked⟩ := terminal_banks_on_completed_path R outward D B
    (traces (cells pivot)) (tails pivot) (terminals pivot) footprint deep slice.upperHeight
    ⟨late, slice.upper_bounds.2⟩
  have equal := MonotoneStrip.collapsed_chain_points_of_contacts (fun k => (cells k).val)
    (fun k => congrArg Complex.re (contacts k slice.upper_bounds))
    (fun k => (terminals k).merged slice.upperHeight
      ⟨(highest k).trans late, slice.upper_bounds.2⟩) 0 pivot
  have physical : origin + (fiveSectorFrame t positive small i).place.symm
      (source.val.upper.point slice.upperHeight) =
        (R.completedRootPath (terminals pivot).vertex).point j s := by
    rw [wall slice.upper_bounds, equal]
    exact tracked
  have bound := B.upper_bank_start_order i (terminals pivot).vertex (terminals pivot).on_cuts
    (terminals pivot).target (terminals pivot).original directions sectors budget (traces source)
    ((traces source).circle_slice_heights radius_positive far slice).2
    ((traces source).circle_slice_width radius_positive slice).2 j s
    ((traces source).regular_of_radius_not_vertexRadii outside
      slice.upper_closed slice.upper_radius)
    physical
  rw [← (terminals pivot).value] at bound
  exact bound

/-- The late entrance crossing on the right lies to the right of the same
selected terminal copy, in the same calibration. -/
theorem late_lower_circle_re_ge_run_terminal_of_contacts (pivot : Fin (n + 1))
    (highest : ∀ k, (terminals k).height ≤ (terminals pivot).height)
    (outside : radius ∉ D.fiveSectorVertexRadii Q (origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point
      (Set.Icc 0 cutoff))
    (late : (terminals pivot).height ≤ slice.lowerHeight) :
    ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).re ≤
      ((traces source).value (source.val.lower.point slice.lowerHeight)).re := by
  obtain ⟨leaf, after_leaf, same_start, _⟩ :=
    terminal_geometric_tail R D B (traces (cells pivot)) (tails pivot) (terminals pivot)
  obtain ⟨_, directions, sectors⟩ := leaf.completed_bank_geometry_from_height R outward
    (terminals pivot).vertex after_leaf
    ((terminals pivot).height_bounds.2.trans (leaf.tail_end_beyond_clip_ball deep))
    same_start curvature_covered
  obtain ⟨j, s, tracked, _⟩ := terminal_banks_on_completed_path R outward D B
    (traces (cells pivot)) (tails pivot) (terminals pivot) footprint deep slice.lowerHeight
    ⟨late, slice.lower_bounds.2⟩
  have equal := MonotoneStrip.collapsed_chain_points_of_contacts (fun k => (cells k).val)
    (fun k => congrArg Complex.re (contacts k slice.lower_bounds))
    (fun k => (terminals k).merged slice.lowerHeight
      ⟨(highest k).trans late, slice.lower_bounds.2⟩) pivot (Fin.last n)
  have physical : origin + (fiveSectorFrame t positive small i).place.symm
      (source.val.lower.point slice.lowerHeight) =
        (R.completedRootPath (terminals pivot).vertex).point j s := by
    rw [wall slice.lower_bounds, ← equal]
    exact tracked
  have bound := B.lower_bank_start_order i (terminals pivot).vertex (terminals pivot).on_cuts
    (terminals pivot).target (terminals pivot).original directions sectors budget (traces source)
    ((traces source).circle_slice_heights radius_positive far slice).1
    ((traces source).circle_slice_width radius_positive slice).1 j s
    ((traces source).regular_of_radius_not_vertexRadii outside
      slice.lower_closed slice.lower_radius)
    physical
  rw [← (terminals pivot).value] at bound
  exact bound

end Unfoldings.ConvexRoof.SectorForest
