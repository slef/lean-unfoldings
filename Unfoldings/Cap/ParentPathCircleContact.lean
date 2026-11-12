module

public import Unfoldings.Cap.ParentPathCircleBankOrder
public import Unfoldings.Cap.CirclePhysicalBankMatching
public import Unfoldings.Cap.CompletedBankClosedContact

/-! Contact between circle endpoints on one actual parent path identifies a physical point. -/

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

/-- Actual closed bank names and closed-chain contact handle branch endpoints too. -/
theorem circle_parent_path_contact_same_point {radius : ℝ}
    (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
    (first_slice : S.BankCircleSlice data.value data.center cutoff radius)
    (last_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
    (directions : ∀ j : Fin (N.spanningCompletion.parents.distanceToRoot w),
      K.projectedVertex (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    (sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (N.completedBankChain w j))
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi)
    (j k : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    (first_regular : ∀ f a, source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) ≠ (K.projectedTriangle f).vertex a)
    (last_regular : ∀ f a, source + (fiveSectorFrame t positive small i).place.symm
      (T.lower.point last_slice.lowerHeight) ≠ (K.projectedTriangle f).vertex a)
    (first_physical : source + (fiveSectorFrame t positive small i).place.symm
      (S.upper.point first_slice.upperHeight) = (N.completedRootPath w).point j s)
    (last_physical : source + (fiveSectorFrame t positive small i).place.symm
      (T.lower.point last_slice.lowerHeight) = (N.completedRootPath w).point k r)
    (same : data.value (S.upper.point first_slice.upperHeight) =
      other.value (T.lower.point last_slice.lowerHeight)) :
    (fiveSectorFrame t positive small i).place.symm (S.upper.point first_slice.upperHeight) =
      (fiveSectorFrame t positive small i).place.symm (T.lower.point last_slice.lowerHeight) := by
  have first_matching := B.circle_upper_physical_eq_exit i data radius_positive far first_slice
    w on_cuts directions j s first_regular first_physical
  have last_matching := B.circle_lower_physical_eq_entrance i other radius_positive far last_slice
    w on_cuts directions k r last_regular last_physical
  have values : data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) =
      other.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight)) := by
    change data.outputFrame.symm (data.value (S.upper.point first_slice.upperHeight)) =
      data.outputFrame.symm (other.value (T.lower.point last_slice.lowerHeight))
    exact congrArg data.outputFrame.symm same
  have banks := first_matching.symm.trans (values.trans last_matching)
  have underlying := B.chain_contact_same_projected_point i (N.completedBankChain w)
    (N.completedBankChain_parent w) sectors directions budget j k s r banks
  have path_equal : (N.completedRootPath w).point j s = (N.completedRootPath w).point k r :=
    (N.completedRootPath_point_bankChain w j s).trans
      (underlying.trans (N.completedRootPath_point_bankChain w k r).symm)
  exact add_left_cancel (first_physical.trans (path_equal.trans last_physical.symm))

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
