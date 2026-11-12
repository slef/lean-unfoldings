module

public import Unfoldings.Cap.BoundaryTerminalSectorAssignment
public import Unfoldings.Cap.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.SectorBoundaryComponents
public import Unfoldings.Cap.GeometricTailBankContacts
public import Unfoldings.Cap.BoundaryRunTerminalPoint

/-! A terminal whose remaining banks follow a sector ray belongs to a pure radial component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}

/-- Agreement on the terminal suffix is physical. The proof also covers a
terminal exactly at its geometric leaf height, without evaluating developed
trace values on any later collapsed bank. -/
theorem boundary_terminal_on_unattached_component
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {S : MonotoneStrip} {ε cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (tails : S.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius radius)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (H : MonotoneHeightGraph)
    (wall : H = (fiveSectorFrame t positive small i).enclosingStrip.lower ∨
      H = (fiveSectorFrame t positive small i).enclosingStrip.upper)
    (agreement : Set.EqOn H.point S.lower.point (Set.Icc continuation.height cutoff)) :
    ∃ c : F.Component, Q.projectedVertex continuation.vertex ∈ (F.componentTail c).carrier ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  obtain ⟨c, member, _, unattached⟩ := boundary_terminal_on_assigned_component R D B data tails
    continuation deep H wall agreement
  exact ⟨c, member, unattached⟩

variable {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
  {Q : ConvexCap FineC}
  (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
  (D : FacewiseDevelopment FineC R.retain)
  (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
  {ε cutoff physicalRadius radius : ℝ} {n : ℕ}
  (cells : Fin (n + 1) → MonotoneStrip)
  (traces : ∀ j, R.RadialStripTraceData positive small D
    (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i (cells j) ε cutoff)
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
    (cells j.succ).lower.point (Set.Icc 0 cutoff))
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces j) physicalRadius radius)
  (tails : ∀ j, (cells j).TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)
  (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))

include contacts tails deep

/-- The highest actual terminal of an initial disappearing run belongs to
one unattached radial component, derived from the enclosing physical ray. -/
theorem first_run_maximum_on_unattached_component
    (pivot : Fin (n + 1)) (highest : ∀ j, (terminals j).height ≤ (terminals pivot).height)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff)) :
    ∃ c : F.Component, Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  exact boundary_terminal_on_unattached_component R D B (traces pivot) (tails pivot)
    (terminals pivot) deep _ (Or.inl rfl)
    (B.first_run_lower_tail_on_boundary i cells traces contacts terminals pivot highest outer)

/-- The final disappearing run has the corresponding genuine radial component. -/
theorem last_run_maximum_on_unattached_component
    (pivot : Fin (n + 1)) (highest : ∀ j, (terminals j).height ≤ (terminals pivot).height)
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff)) :
    ∃ c : F.Component, Q.projectedVertex (terminals pivot).vertex ∈ (F.componentTail c).carrier ∧
      ∀ e : {w : C.Vertex Set.univ // w ∉ M.parents.roots},
        M.cutPieceLabel F covered (Sum.inl e) ≠ c := by
  exact boundary_terminal_on_unattached_component R D B (traces pivot) (tails pivot)
    (terminals pivot) deep _ (Or.inr rfl)
    (fun _ member => (B.last_run_lower_tail_on_boundary i cells traces contacts terminals
      pivot highest outer member).symm)

end Unfoldings.ConvexCap.SectorForest
