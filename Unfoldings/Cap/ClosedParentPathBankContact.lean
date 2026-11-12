module

public import Unfoldings.Cap.ClosedParentPathBankMatching
public import Unfoldings.Cap.CompletedBankClosedContact

/-! Closed parent-path bank contacts identify physical points at every height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {S T : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (other : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i T ε cutoff)

/-- Actual closed matching intervals replace all vertex-height and circle-radius exclusions. -/
theorem closed_parent_path_bank_contact_same_point
    (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (first_pinches : S.ApproachedPinchesIn
      (Set.range (fun v : {v : C.Vertex Set.univ // K.projectedVertex v ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex v.val - source))) 0 cutoff)
    (last_pinches : T.ApproachedPinchesIn
      (Set.range (fun v : {v : C.Vertex Set.univ // K.projectedVertex v ∈ cuts} =>
        (fiveSectorFrame t positive small i).place (K.projectedVertex v.val - source))) 0 cutoff)
    {a b c d : ℝ} (first_start : 0 ≤ a) (first_order : a < b) (first_finish : b ≤ cutoff)
    (last_start : 0 ≤ c) (last_order : c < d) (last_finish : d ≤ cutoff)
    (first_closed : ∀ h ∈ Set.Ioo a b, S.upper.point h ∈ closure data.strictDomain)
    (last_closed : ∀ h ∈ Set.Ioo c d, T.lower.point h ∈ closure other.strictDomain)
    (first_tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
          (N.completedRootPath w).point j s)
    (last_tracked : ∀ h ∈ Set.Ioo c d,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (T.lower.point h) =
          (N.completedRootPath w).point j s)
    {h k : ℝ} (first_height : h ∈ Set.Icc a b) (last_height : k ∈ Set.Icc c d)
    (same : data.value (S.upper.point h) = other.value (T.lower.point k)) :
    (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
      (fiveSectorFrame t positive small i).place.symm (T.lower.point k) := by
  obtain ⟨j, s, first_physical, first_value⟩ :=
    B.upper_matches_completed_path_on_closed_interval i w on_cuts directions data first_pinches
      first_start first_order first_finish first_closed first_tracked h first_height
  obtain ⟨l, r, last_physical, last_value⟩ :=
    B.lower_matches_completed_path_on_closed_interval i w on_cuts directions other last_pinches
      last_start last_order last_finish last_closed last_tracked k last_height
  have values := first_value.symm.trans (same.trans last_value)
  have banks := (B.sectorFrame i).injective values
  have underlying := B.chain_contact_same_projected_point i (N.completedBankChain w)
    (N.completedBankChain_parent w) sectors directions budget j l s r banks
  have physical : (N.completedRootPath w).point j s = (N.completedRootPath w).point l r :=
    (N.completedRootPath_point_bankChain w j s).trans
      (underlying.trans (N.completedRootPath_point_bankChain w l r).symm)
  exact add_left_cancel (first_physical.trans (physical.trans last_physical.symm))

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
