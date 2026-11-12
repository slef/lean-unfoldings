module

public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.CompletedSectorQuadrants
public import Unfoldings.Geometry.HeightGraphAffineOrder
public import Unfoldings.Geometry.FiniteWaterfall

/-! Actual visible traces progress in both coordinates along a geometric cut tail. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)

/-- Every fine chart is positive on every whole coarse edge of this tail. This
uses the shared direction sector, with no coarse-to-fine edge correspondence. -/
theorem centered_chart_tail_edges_positive
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    (Q : ConvexCap FineC)
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (f : FineFace)
    (j : Fin ((M.geometricParents F covered positive small lower).distanceToRoot leaf.val)) :
    let P := M.geometricRootPath F covered positive small lower
      (fiveSectorFrame t positive small i).place leaf.val
    let A := D.centeredCoordinatePlacement Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
      (fiveSectorFrame t positive small i).place f
    0 < (A.linear (P.edge j)).re ∧ 0 < (A.linear (P.edge j)).im := by
  let z := (M.geometricParent F covered)^[j.val] leaf.val
  have nonroot : z ∉ (M.geometricParents F covered positive small lower).roots :=
    (M.geometricParents F covered positive small lower).iterate_lt_distanceToRoot_not_mem
      leaf.val j.isLt
  have direction := leaf.component_directions z nonroot
    (M.geometricComponent_iterate F covered leaf.val j.val)
  have nonzero : F.geometricPosition (M.geometricParent F covered z) -
      F.geometricPosition z ≠ 0 := by
    intro zero
    have equal := F.geometricPosition_injective lower (sub_eq_zero.mp zero)
    have ascending := (M.geometricParents F covered positive small lower).ascending z nonroot
    change (M.geometricParents F covered positive small lower).height z <
      (M.geometricParents F covered positive small lower).height
        (M.geometricParent F covered z) at ascending
    rw [equal] at ascending
    exact lt_irrefl _ ascending
  dsimp only
  rw [D.centeredCoordinatePlacement_linear, M.geometricRootPath_edge,
    D.coordinatePlacement_linear, LinearIsometryEquiv.symm_apply_apply]
  exact B.quadrants i f _ direction nonzero

/-- Both coordinates of the same actual continuous trace are nondecreasing
along a visible tail interval, including its approached terminal pinch. -/
theorem developed_tail_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    {a b : ℝ} (start : leaf.point.re + leaf.point.im ≤ a) (ordered : a ≤ b)
    (finish : b < M.geometricTailEndHeight F covered positive small lower i leaf.val)
    (closed : ∀ h ∈ Set.Icc a b, leaf.tailGraph.graph.point h ∈ closure data.strictDomain) :
    (data.value (leaf.tailGraph.graph.point a)).re ≤
        (data.value (leaf.tailGraph.graph.point b)).re ∧
      (data.value (leaf.tailGraph.graph.point a)).im ≤
        (data.value (leaf.tailGraph.graph.point b)).im := by
  let P := M.geometricRootPath F covered positive small lower
    (fiveSectorFrame t positive small i).place leaf.val
  let A := fun f : FineFace => (D.centeredCoordinatePlacement Q (K.projectedVertex origin)
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
    (fiveSectorFrame t positive small i).place f).toAffineMap
  have order (L : ℂ →ₗ[ℝ] ℝ)
      (test : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ z.im → 0 ≤ L z) :
      L (data.value (leaf.tailGraph.graph.point a)) ≤
        L (data.value (leaf.tailGraph.graph.point b)) := by
    apply P.heightGraph_finite_selection_order leaf.tailGraph.graph leaf.tailGraph.pieces
      (fun j => add_pos (leaf.tailGraph.positive_steps j).1 (leaf.tailGraph.positive_steps j).2)
      (fun f => L.toAffineMap.comp (A f))
      (fun f => L.continuous_of_finiteDimensional.comp (A f).continuous_of_finiteDimensional)
      (fun f j => test _ (leaf.centered_chart_tail_edges_positive Q R D B f j).1.le
        (leaf.centered_chart_tail_edges_positive Q R D B f j).2.le)
      (L.continuous_of_finiteDimensional.comp data.continuous) start ordered finish
    intro h member
    obtain ⟨f, _, _, value⟩ := data.visible_closure (closed h member)
    exact ⟨f, congrArg L value⟩
  exact ⟨order Complex.reCLM.toLinearMap (fun _ h _ => h),
    order Complex.imCLM.toLinearMap (fun _ _ h => h)⟩

/-- A completed physical bank supplies the whole visible tail interval from
its final approached point; no choice of visible charts is required. -/
theorem developed_bank_tail_interval_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    {H : MonotoneHeightGraph} (bank : H = S.lower ∨ H = S.upper)
    {a b : ℝ} (start : leaf.point.re + leaf.point.im ≤ a) (ordered : a ≤ b)
    (finish : b < M.geometricTailEndHeight F covered positive small lower i leaf.val)
    (agreement : Set.EqOn H.point leaf.tailGraph.graph.point (Set.Icc a b))
    (endpoint : H.point b ∈ closure data.strictDomain) :
    (data.value (H.point a)).re ≤ (data.value (H.point b)).re ∧
      (data.value (H.point a)).im ≤ (data.value (H.point b)).im := by
  have nonnegative : 0 ≤ a :=
    (add_nonneg leaf.point_nonnegative.1 leaf.point_nonnegative.2).trans start
  have closed (h : ℝ) (bounds : h ∈ Set.Icc a b) :
      leaf.tailGraph.graph.point h ∈ closure data.strictDomain := by
    rw [← agreement bounds]
    have height : h ∈ Set.Icc 0 ((H.point b).re + (H.point b).im) := by
      rw [H.point_height]
      exact ⟨nonnegative.trans bounds.1, bounds.2⟩
    rcases bank with rfl | rfl
    · exact data.lower_bank_closed_before endpoint height
    · exact data.upper_bank_closed_before endpoint height
  rw [agreement ⟨le_rfl, ordered⟩, agreement ⟨ordered, le_rfl⟩]
  exact leaf.developed_tail_order R D B data start ordered finish closed

/-- Retain the complete-tail bank interface. -/
theorem developed_completed_bank_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    {H : MonotoneHeightGraph} (bank : H = S.lower ∨ H = S.upper)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    {a b : ℝ} (start : leaf.point.re + leaf.point.im ≤ a) (ordered : a ≤ b)
    (within : b ≤ cutoff)
    (finish : b < M.geometricTailEndHeight F covered positive small lower i leaf.val)
    (endpoint : H.point b ∈ closure data.strictDomain) :
    (data.value (H.point a)).re ≤ (data.value (H.point b)).re ∧
      (data.value (H.point a)).im ≤ (data.value (H.point b)).im := by
  have point (h : ℝ) (bounds : h ∈ Set.Icc a b) : H.point h = leaf.tailGraph.graph.point h := by
    apply Complex.ext
    · exact completion.2 h ⟨start.trans bounds.1, bounds.2.trans within⟩
    · change h - H.coordinate h = h - leaf.tailGraph.graph.coordinate h
      rw [completion.2 h ⟨start.trans bounds.1, bounds.2.trans within⟩]
  exact leaf.developed_bank_tail_interval_order R D B data bank start ordered finish
    (fun h bounds => point h bounds) endpoint

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
