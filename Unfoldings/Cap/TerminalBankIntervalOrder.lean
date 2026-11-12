module

public import Unfoldings.Cap.SameSectorEmptyCircleComparison
public import Unfoldings.Cap.GeometricTailTraceOrder

/-! An approached bank following a collapsed strip's actual tail progresses in both coordinates. -/

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

/-- Physical bank agreement is needed only on the actual interval being
compared. No complete prefix identity or independently chosen fine path is supplied. -/
theorem terminal_tail_bank_interval_order_from_height
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {U V : MonotoneStrip} {ε δ cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
    (tails : U.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius radius)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i V δ cutoff)
    {H : MonotoneHeightGraph} (bank : H = V.lower ∨ H = V.upper)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {a b : ℝ} (start : continuation.height ≤ a) (ordered : a ≤ b) (within : b ≤ cutoff)
    (agreement : Set.EqOn H.point U.lower.point (Set.Icc a b))
    (endpoint : H.point b ∈ closure other.strictDomain) :
    (other.value (H.point a)).re ≤ (other.value (H.point b)).re ∧
      (other.value (H.point a)).im ≤ (other.value (H.point b)).im := by
  obtain ⟨leaf, after_leaf, _, follows⟩ := terminal_geometric_tail R D B data tails continuation
  apply leaf.developed_bank_tail_interval_order R D B other bank (after_leaf.trans start) ordered
    (within.trans_lt (leaf.tail_end_beyond_clip_ball deep)) _ endpoint
  intro h member
  exact (agreement member).trans (follows h ⟨start.trans member.1, member.2.trans within⟩).1

/-- Retain the terminal-start interval interface. -/
theorem terminal_tail_bank_interval_order
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    {U V : MonotoneStrip} {ε δ cutoff physicalRadius radius : ℝ}
    (data : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i U ε cutoff)
    (tails : U.TerminalTailsFrom
      (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
      (fun leaf => leaf.tailGraph.graph) cutoff)
    (continuation : B.EmptyCircleContinuation i data physicalRadius radius)
    (other : R.RadialStripTraceData positive small D
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) i V δ cutoff)
    {H : MonotoneHeightGraph} (bank : H = V.lower ∨ H = V.upper)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    {b : ℝ} (ordered : continuation.height ≤ b) (within : b ≤ cutoff)
    (agreement : Set.EqOn H.point U.lower.point (Set.Icc continuation.height b))
    (endpoint : H.point b ∈ closure other.strictDomain) :
    (other.value (H.point continuation.height)).re ≤ (other.value (H.point b)).re ∧
      (other.value (H.point continuation.height)).im ≤ (other.value (H.point b)).im := by
  exact terminal_tail_bank_interval_order_from_height R D B data tails continuation other bank
    deep le_rfl ordered within agreement endpoint

end Unfoldings.ConvexCap.SectorForest
