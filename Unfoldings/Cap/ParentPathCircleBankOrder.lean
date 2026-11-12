module

public import Unfoldings.Cap.RadialStripCircleComparison
public import Unfoldings.Cap.CompletedComparisonProgress
public import Unfoldings.Cap.CompletedTraceVertexCopy
public import Unfoldings.Cap.RadialStripBankOrder
public import Unfoldings.Cap.CircleStripSeparation

/-! Actual facing strip-circle endpoints on one outward cut path have the derived bank order. -/

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

/-- Named chart matching and the actual complete-bank comparison derive this order.
The caller identifies physical parent-path points; it supplies no developed gap-order
certificate, comparison curve, or bank copy at the starting vertex. -/
theorem circle_parent_path_bank_order {μ radius : ℝ} (small_error : ε < μ)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
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
      (T.lower.point last_slice.lowerHeight) = (N.completedRootPath w).point k r) :
    (data.value (S.upper.point first_slice.upperHeight) - data.center).re ≤
        (other.value (T.lower.point last_slice.lowerHeight) - other.center).re ∧
      (other.value (T.lower.point last_slice.lowerHeight) - other.center).im ≤
        (data.value (S.upper.point first_slice.upperHeight) - data.center).im := by
  obtain ⟨f, on_face⟩ := Set.mem_iUnion.mp
    (K.footprint_eq_union_projectedTriangles.subset (K.projectedVertex_mem_footprint w))
  obtain ⟨target, original, _⟩ :=
    N.exists_boundary_copy_of_face_vertex (N.completedDevelopment D) w f on_face
  let origin := (N.completedDevelopment D).boundaryPosition (N.completedContour.cycle.point target)
  have first_value := B.circle_upper_eq_exit_comparison_point i data radius_positive far
    first_slice w on_cuts directions origin j s first_regular first_physical
  have last_value := B.circle_lower_eq_entrance_comparison_point i other radius_positive far
    last_slice w on_cuts directions origin k r last_regular last_physical
  have first_height := data.closed_height_pos_of_norm first_slice.upper_closed
    (by rw [first_slice.upper_radius]; exact radius_positive)
  have last_height := other.closed_height_pos_of_norm last_slice.lower_closed
    (by rw [last_slice.lower_radius]; exact radius_positive)
  have first_quadrant := data.strict_quadrant_of_closed_margin small_error first_margin
    first_slice.upper_closed first_height
  have last_quadrant := other.strict_quadrant_of_closed_margin small_error last_margin
    last_slice.lower_closed last_height
  have same_radius :
      ‖(B.exitComparisonChain i w origin).point ⟨2 * j.val + 1, by omega⟩ s - data.center‖ =
        ‖(B.entranceComparisonChain i w origin).point
          ⟨2 * k.val + 1, by omega⟩ r - data.center‖ := by
    rw [← first_value, ← last_value, first_slice.upper_radius]
    exact last_slice.lower_radius.symm
  have order := B.comparisonChains_circle_order i w target original sectors budget directions
    data.center ⟨2 * j.val + 1, by omega⟩ ⟨2 * k.val + 1, by omega⟩ s r
    (by rw [← first_value]; exact ⟨first_quadrant.1.le, first_quadrant.2.le⟩)
    (by rw [← last_value]; exact ⟨last_quadrant.1.le, last_quadrant.2.le⟩) same_radius
  rw [← first_value, ← last_value] at order
  exact order

/-- The derived facing-bank order separates both actual open strip-circle images.
Weak gap order allows boundary contact; it does not allow interior overlap. -/
theorem circle_parent_path_slices_disjoint {μ radius : ℝ} (nonnegative : 0 ≤ ε)
    (small_error : ε < 1 / 2) (numerical : ε * (1 + ε) < μ - ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K
        (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference)
        (fiveSectorFrame t positive small i).place f).linear z - z‖ ≤ ε * ‖z‖)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
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
      (T.lower.point last_slice.lowerHeight) = (N.completedRootPath w).point k r) :
    Disjoint (data.value '' S.openSlab 0 cutoff ∩ {z | ‖z - data.center‖ = radius})
      (other.value '' T.openSlab 0 cutoff ∩ {z | ‖z - other.center‖ = radius}) := by
  have close_margin : ε < μ := by nlinarith [sq_nonneg ε]
  have gap := B.circle_parent_path_bank_order i data other close_margin first_margin last_margin
    radius_positive far first_slice last_slice w on_cuts directions sectors budget j k s r
    first_regular last_regular first_physical last_physical
  have first_order := data.bank_circle_order nonnegative small_error numerical linear_error
    first_margin radius_positive first_slice.lower_closed first_slice.upper_closed
    first_slice.lower_radius first_slice.upper_radius first_slice.distinct
  have last_order := other.bank_circle_order nonnegative small_error numerical linear_error
    last_margin radius_positive last_slice.lower_closed last_slice.upper_closed
    last_slice.lower_radius last_slice.upper_radius last_slice.distinct
  apply first_slice.disjoint_circle_images_of_bank_order last_slice first_order.1 last_order.1 gap.1
  rintro z ⟨p, member, rfl⟩
  exact data.strict_quadrant_of_margin close_margin first_margin member

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
