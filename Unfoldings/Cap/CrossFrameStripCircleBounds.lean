module

public import Unfoldings.Cap.CrossFrameInnerTerminalSeparation
public import Unfoldings.Cap.StripCirclePointBounds
public import Unfoldings.Cap.RadialStripPhysicalMap
public import Unfoldings.Cap.RadialStripPointOrder

/-! Apply actual cross-frame bank barriers to the constructed waterfall circle images. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))

theorem circle_image_open_bank_bounds (i : FiveSector) {S : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (ordered : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    {μ : ℝ} (small_error : ε < μ)
    (margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) {p : Plane}
    (member : p ∈ data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius})) :
    0 < (B.sectorFrame i (p - D.projectedMap K source)).re ∧
      0 < (B.sectorFrame i (p - D.projectedMap K source)).im ∧
      (B.sectorFrame i (p - D.projectedMap K source)).re <
        (data.value (S.upper.point slice.upperHeight) - data.center).re ∧
      (B.sectorFrame i (p - D.projectedMap K source)).im <
        (data.value (S.lower.point slice.lowerHeight) - data.center).im ∧
      ‖p - D.projectedMap K source‖ = radius := by
  obtain ⟨_, ⟨⟨x, inside, rfl⟩, size⟩, at_p⟩ := member
  have quadrant := data.strict_quadrant_of_margin small_error margin inside
  have on_circle : data.value x ∈ data.value '' S.openSlab 0 cutoff ∩
      {z | ‖z - data.center‖ = radius} := ⟨⟨x, inside, rfl⟩, size⟩
  have horizontal := slice.re_bounds_of_mem_circle_image ordered
    ⟨quadrant.1.le, quadrant.2.le⟩ on_circle
  have lower_height := data.closed_height_pos_of_norm slice.lower_closed
    (by rw [slice.lower_radius]; exact radius_positive)
  have lower_quadrant := data.strict_quadrant_of_closed_margin small_error margin
    slice.lower_closed lower_height
  have vertical := slice.im_lt_lower_of_mem_circle_image ordered
    ⟨lower_quadrant.1.le, lower_quadrant.2.le⟩ ⟨quadrant.1.le, quadrant.2.le⟩ on_circle
  have centered : B.sectorFrame i (p - D.projectedMap K source) =
      data.value x - data.center := by
    change data.outputFrame (p - D.projectedMap K source) = _
    rw [← at_p, map_sub, LinearIsometryEquiv.apply_symm_apply, ← data.center_eq_outputFrame]
  have physical_size : ‖p - D.projectedMap K source‖ = radius := by
    rw [← at_p, data.outputFrame_symm_source_distance]
    exact size
  rw [centered]
  exact ⟨quadrant.1, quadrant.2, horizontal.2, vertical, physical_size⟩

/-- Both bounding points belong to one actual fine bank chain. Bounds from
early terminal records and exact late circle matching can be used independently
on either side; no developed gap order between the sectors is assumed. -/
theorem circle_images_disjoint_of_actual_bank_chain_bounds
    (i l : FiveSector) {S T : MonotoneStrip} {ε cutoff radius : ℝ}
    (data : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
    (other : N.RadialStripTraceData positive small D
      (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) l T ε cutoff)
    (slice : S.BankCircleSlice data.value data.center cutoff radius)
    (other_slice : T.BankCircleSlice other.value other.center cutoff radius)
    (first_order : (data.value (S.lower.point slice.lowerHeight) - data.center).re <
      (data.value (S.upper.point slice.upperHeight) - data.center).re)
    (last_order : (other.value (T.lower.point other_slice.lowerHeight) - other.center).re <
      (other.value (T.upper.point other_slice.upperHeight) - other.center).re)
    {μ ν : ℝ} (first_error : ε < μ) (last_error : ε < ν)
    (first_margin : ∀ z ∈ S.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (last_margin : ∀ z ∈ T.carrier, 0 ≤ z.re + z.im →
      ν * (z.re + z.im) ≤ z.re ∧ ν * (z.re + z.im) ≤ z.im)
    (radius_positive : 0 < radius) {n : ℕ}
    (chain : Fin n → {v : C.Vertex Set.univ // v ∉ N.spanningCompletion.parents.roots})
    (parents : ∀ j k : Fin n, k.val = j.val + 1 →
      N.spanningCompletion.parents.parent (chain j).val = (chain k).val)
    (first_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) i (chain j))
    (last_sectors : ∀ j, N.CurvedSubtreeInSector (t := t) l (chain j))
    (first_directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) - K.projectedVertex (chain j).val ∈
        closedFiveSector t i)
    (last_directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (chain j).val) - K.projectedVertex (chain j).val ∈
        closedFiveSector t l)
    (budget : C.totalInteriorAngularDefect Set.univ ≤ Real.pi)
    (j k : Fin n) (s r : unitInterval)
    (exit_inside : ‖N.parentExitPoint (N.completedDevelopment D) (chain j) (1 - (s : ℝ)) -
      D.projectedMap K source‖ ≤ radius)
    (entrance_inside : ‖N.parentEntrancePoint (N.completedDevelopment D) (chain k) (1 - (r : ℝ)) -
      D.projectedMap K source‖ ≤ radius)
    (quadrants : ∀ a, a = i ∨ a = l →
      (0 < (B.sectorFrame a
        (N.parentExitPoint (N.completedDevelopment D) (chain j) (1 - (s : ℝ)) -
          D.projectedMap K source)).re ∧
       0 < (B.sectorFrame a
        (N.parentExitPoint (N.completedDevelopment D) (chain j) (1 - (s : ℝ)) -
          D.projectedMap K source)).im) ∧
      (0 < (B.sectorFrame a
        (N.parentEntrancePoint (N.completedDevelopment D) (chain k) (1 - (r : ℝ)) -
          D.projectedMap K source)).re ∧
       0 < (B.sectorFrame a
        (N.parentEntrancePoint (N.completedDevelopment D) (chain k) (1 - (r : ℝ)) -
          D.projectedMap K source)).im))
    (first_bound : (data.value (S.upper.point slice.upperHeight) - data.center).re ≤
      (B.sectorFrame i
        (N.parentExitPoint (N.completedDevelopment D) (chain j) (1 - (s : ℝ)) -
          D.projectedMap K source)).re)
    (last_bound : (other.value (T.lower.point other_slice.lowerHeight) - other.center).im ≤
      (B.sectorFrame l
        (N.parentEntrancePoint (N.completedDevelopment D) (chain k) (1 - (r : ℝ)) -
          D.projectedMap K source)).im) :
    Disjoint (data.outputFrame.symm '' (data.value '' S.openSlab 0 cutoff ∩
        {z | ‖z - data.center‖ = radius}))
      (other.outputFrame.symm '' (other.value '' T.openSlab 0 cutoff ∩
        {z | ‖z - other.center‖ = radius})) := by
  have first_bounds := fun {p : Plane} => B.circle_image_open_bank_bounds i data slice first_order
    first_error first_margin radius_positive (p := p)
  have last_bounds := fun {p : Plane} =>
    B.circle_image_open_bank_bounds l other other_slice last_order
      last_error last_margin radius_positive (p := p)
  apply B.chain_points_circle_separation i l chain parents first_sectors last_sectors
    first_directions last_directions budget j k s r (D.projectedMap K source)
    exit_inside entrance_inside (quadrants i (Or.inl rfl)).1 (quadrants l (Or.inr rfl)).1
    (quadrants i (Or.inl rfl)).2 (quadrants l (Or.inr rfl)).2
  · intro p member
    have bounds := first_bounds member
    exact ⟨bounds.1.le, bounds.2.1, bounds.2.2.1.trans_le first_bound⟩
  · intro p member
    have bounds := last_bounds member
    exact ⟨bounds.1.le, bounds.2.1, bounds.2.2.2.1.trans_le last_bound⟩
  · intro p member
    exact (first_bounds member).2.2.2.2
  · intro p member
    exact (last_bounds member).2.2.2.2

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
