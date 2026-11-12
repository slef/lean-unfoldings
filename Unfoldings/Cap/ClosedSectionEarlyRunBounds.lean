module

public import Unfoldings.Cap.TerminalRunEarlyBoundsContacts
public import Unfoldings.Cap.ClosedBankPropertyLimit
public import Unfoldings.Cap.ClosedBankCircleCrossing
public import Unfoldings.Cap.ClosedEmptyCircleRunRadiusGap
public import Unfoldings.Cap.TerminalHeightUniqueness
public import Unfoldings.Cap.RadialClosedCircleSections

/-! Early terminal bounds persist at every closed circle section, including vertex radii. -/

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

variable
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (outward : R.Outward) (D : FacewiseDevelopment FineC R.retain)
    (B : R.FiveSectorFrameData positive small (R.completedDevelopment D))
    (leaf_vertices : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      ∃ w : FineC.Vertex Set.univ, Q.projectedVertex w = F.geometricPosition leaf.val)
    (footprint : Q.footprint = K.clipFootprint Z) {cutoff : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
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
          (Q.projectedVertex v.val - K.projectedVertex origin))) 0 cutoff)

variable {n : ℕ} (cells : Fin (n + 1) → {S : MonotoneStrip // S ∈ P.cells})
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).val.upper.point
    (cells j.succ).val.lower.point (Set.Icc 0 cutoff))
  (ordered_cells : ∀ a b : Fin (n + 1), a < b → List.Sublist [cells a, cells b] P.cells.attach)
  {physicalRadius radius : ℝ}
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces (cells j)) physicalRadius radius)
  (tails : ∀ j, (cells j).val.TerminalTailsFrom
    (fun leaf : M.GeometricSectorLeaf F covered positive small lower i => leaf.point)
    (fun leaf => leaf.tailGraph.graph) cutoff)

variable
  (provenance : ∀ H ∈ P.separators,
    ∃ leaf : M.GeometricSectorLeaf F covered positive small lower i,
      leaf.point.re + leaf.point.im ≤ cutoff ∧
        MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (represented : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    leaf.point.re + leaf.point.im ≤ cutoff → ∃ H ∈ P.separators,
      MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
  (leaf_coherent : ∀ leaf : M.GeometricSectorLeaf F covered positive small lower i,
    D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
  (source : {S : MonotoneStrip // S ∈ P.cells})
  (slice : source.val.ClosedBankCircleSection
    (traces source).value (traces source).center cutoff radius)
  (radius_positive : 0 < radius) (far : radius < (1 / 2 - ε) * cutoff)
  (empty : ∀ k, (traces (cells k)).value '' closure ((cells k).val.openSlab 0 cutoff) ∩
    {z | ‖z - (traces (cells k)).center‖ = radius} = ∅)
  (continuations : ∀ r ∈ Set.Ioo 0 radius, ∀ k,
    r ∉ (traces (cells k)).emptyCircleExceptions →
    (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
      {z | ‖z - (traces (cells k)).center‖ = r} = ∅ →
    Nonempty (B.EmptyCircleContinuation i (traces (cells k)) physicalRadius r))


include outward leaf_vertices footprint deep curvature_covered budget nonnegative
  small_error linear_error pinches contacts ordered_cells tails provenance represented
  leaf_coherent radius_positive far empty continuations

/-- The upper early bound includes genuine and collapsed closed circle sections. -/
theorem closed_section_early_upper_re_le_first_run_maximum
    {μ : ℝ} (close_margin : ε < μ)
    (margin : ∀ z ∈ source.val.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (pivot : Fin (n + 1))
    (strict_before : ∀ k : Fin (n + 1), k < pivot →
      (terminals k).height < (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [source, cells k] P.cells.attach)
    (wall : Set.EqOn source.val.upper.point (cells 0).val.lower.point (Set.Icc 0 cutoff))
    (separator : source.val.upper ∈ P.separators)
    (early : slice.upperHeight ≤ (terminals pivot).height) :
    ((traces source).value (source.val.upper.point slice.upperHeight)).re ≤
      ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).re
      := by
  classical
  obtain ⟨lower_radius, lower_nonnegative, lower_lt, absent⟩ :=
    RadialCutForest.exists_common_inner_radius_of_empty_closed_circles
      (fun j => traces (cells j)) radius_positive far empty
  let exception := D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small ∪
    ⋃ k : Fin (n + 1), (traces (cells k)).emptyCircleExceptions
  have finite : exception.Finite :=
    (D.finite_fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
      positive small).union (Set.finite_iUnion fun k =>
        (traces (cells k)).finite_emptyCircleExceptions)
  obtain ⟨_, active⟩ := closure_nonempty_iff.mp ⟨_, slice.upper_closed⟩
  apply (traces source).radial.closed_bank_property_at_radius_limit
    (traces source).continuous source.val.upper (Or.inr rfl)
    ((traces source).source_bank_values active).2
    slice.upper_bounds.1 radius_positive slice.upper_closed slice.upper_radius
    lower_lt finite
    (isClosed_le (Complex.continuous_re.comp
      ((traces source).continuous.comp source.val.upper.point_continuous)) continuous_const)
  intro r bounds outside
  have r_bounds : r ∈ Set.Ioo 0 radius :=
    ⟨lower_nonnegative.trans_lt bounds.1, bounds.2⟩
  have far_r := bounds.2.trans far
  have outside_vertices : r ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small :=
    fun member => outside (Or.inl member)
  have outside_empty (k : Fin (n + 1)) : r ∉ (traces (cells k)).emptyCircleExceptions :=
    fun member => outside (Or.inr (Set.mem_iUnion.mpr ⟨k, member⟩))
  have empty_open (k : Fin (n + 1)) :
      (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
        {z | ‖z - (traces (cells k)).center‖ = r} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨⟨z, member, rfl⟩, size⟩
    have belongs : (traces (cells k)).value z ∈
        (traces (cells k)).value '' closure ((cells k).val.openSlab 0 cutoff) ∩
          {z | ‖z - (traces (cells k)).center‖ = r} :=
      ⟨⟨z, subset_closure member, rfl⟩, size⟩
    rw [absent r bounds.1 k] at belongs
    exact belongs
  let nearby := fun k => Classical.choice
    (continuations r r_bounds k (outside_empty k) (empty_open k))
  have heights (k) : (nearby k).height = (terminals k).height :=
    (nearby k).height_eq (terminals k)
  obtain ⟨k, k_bounds, k_closed, k_size⟩ :=
    (traces source).exists_closed_bank_point_on_smaller_circle source.val.upper
      (Or.inr rfl) slice.upper_bounds.1 slice.upper_closed slice.upper_radius r_bounds
  have approached := (traces source).closed_circle_point_mem_closure_openSlab
    r_bounds.1 far_r k_closed k_size
  obtain ⟨r_slice⟩ := (traces source).circle_slice_of_approached_point_off_vertexRadii
    (pinches source) close_margin margin r_bounds.1 far_r outside_vertices approached k_size
  have smaller_height := (traces source).circle_slice_upper_height_le_closed_height
    slice.upper_bounds.1 slice.upper_closed slice.upper_radius r_bounds r_slice
  have bound := early_upper_circle_re_le_first_run_maximum_of_contacts R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches cells contacts ordered_cells nearby tails provenance represented
    leaf_coherent source r_slice r_bounds.1 far_r outside_vertices outside_empty empty_open
    pivot (by
      intro k ordered
      simpa only [heights k, heights pivot] using strict_before k ordered)
    source_order wall separator (by rw [heights pivot]; exact smaller_height.trans early)
  rw [heights pivot] at bound
  exact ⟨r_slice.upperHeight, r_slice.upper_bounds, r_slice.upper_closed,
    r_slice.upper_radius, bound⟩

/-- The lower early bound includes genuine and collapsed closed circle sections. -/
theorem closed_section_early_lower_im_le_last_run_maximum
    {μ : ℝ} (close_margin : ε < μ)
    (margin : ∀ z ∈ source.val.carrier, 0 ≤ z.re + z.im →
      μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (pivot : Fin (n + 1))
    (strict_after : ∀ k : Fin (n + 1), pivot < k →
      (terminals k).height < (terminals pivot).height)
    (source_order : ∀ k, List.Sublist [cells k, source] P.cells.attach)
    (wall : Set.EqOn source.val.lower.point (cells (Fin.last n)).val.upper.point (Set.Icc 0 cutoff))
    (separator : source.val.lower ∈ P.separators)
    (early : slice.lowerHeight ≤ (terminals pivot).height) :
    ((traces source).value (source.val.lower.point slice.lowerHeight)).im ≤
      ((traces (cells pivot)).value ((cells pivot).val.lower.point (terminals pivot).height)).im
      := by
  classical
  obtain ⟨lower_radius, lower_nonnegative, lower_lt, absent⟩ :=
    RadialCutForest.exists_common_inner_radius_of_empty_closed_circles
      (fun j => traces (cells j)) radius_positive far empty
  let exception := D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small ∪
    ⋃ k : Fin (n + 1), (traces (cells k)).emptyCircleExceptions
  have finite : exception.Finite :=
    (D.finite_fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference)
      positive small).union (Set.finite_iUnion fun k =>
        (traces (cells k)).finite_emptyCircleExceptions)
  obtain ⟨_, active⟩ := closure_nonempty_iff.mp ⟨_, slice.lower_closed⟩
  apply (traces source).radial.closed_bank_property_at_radius_limit
    (traces source).continuous source.val.lower (Or.inl rfl)
    ((traces source).source_bank_values active).1
    slice.lower_bounds.1 radius_positive slice.lower_closed slice.lower_radius
    lower_lt finite
    (isClosed_le (Complex.continuous_im.comp
      ((traces source).continuous.comp source.val.lower.point_continuous)) continuous_const)
  intro r bounds outside
  have r_bounds : r ∈ Set.Ioo 0 radius :=
    ⟨lower_nonnegative.trans_lt bounds.1, bounds.2⟩
  have far_r := bounds.2.trans far
  have outside_vertices : r ∉ D.fiveSectorVertexRadii Q (K.projectedVertex origin)
      (R.calibratedFrame (R.completedDevelopment D) B.anchor B.reference) positive small :=
    fun member => outside (Or.inl member)
  have outside_empty (k : Fin (n + 1)) : r ∉ (traces (cells k)).emptyCircleExceptions :=
    fun member => outside (Or.inr (Set.mem_iUnion.mpr ⟨k, member⟩))
  have empty_open (k : Fin (n + 1)) :
      (traces (cells k)).value '' (cells k).val.openSlab 0 cutoff ∩
        {z | ‖z - (traces (cells k)).center‖ = r} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨⟨z, member, rfl⟩, size⟩
    have belongs : (traces (cells k)).value z ∈
        (traces (cells k)).value '' closure ((cells k).val.openSlab 0 cutoff) ∩
          {z | ‖z - (traces (cells k)).center‖ = r} :=
      ⟨⟨z, subset_closure member, rfl⟩, size⟩
    rw [absent r bounds.1 k] at belongs
    exact belongs
  let nearby := fun k => Classical.choice
    (continuations r r_bounds k (outside_empty k) (empty_open k))
  have heights (k) : (nearby k).height = (terminals k).height :=
    (nearby k).height_eq (terminals k)
  obtain ⟨k, k_bounds, k_closed, k_size⟩ :=
    (traces source).exists_closed_bank_point_on_smaller_circle source.val.lower
      (Or.inl rfl) slice.lower_bounds.1 slice.lower_closed slice.lower_radius r_bounds
  have approached := (traces source).closed_circle_point_mem_closure_openSlab
    r_bounds.1 far_r k_closed k_size
  obtain ⟨r_slice⟩ := (traces source).circle_slice_of_approached_point_off_vertexRadii
    (pinches source) close_margin margin r_bounds.1 far_r outside_vertices approached k_size
  have smaller_height := (traces source).circle_slice_lower_height_le_closed_height
    slice.lower_bounds.1 slice.lower_closed slice.lower_radius r_bounds r_slice
  have bound := early_lower_circle_im_le_last_run_maximum_of_contacts R outward D B
    leaf_vertices footprint deep P traces curvature_covered budget nonnegative small_error
    linear_error pinches cells contacts ordered_cells nearby tails provenance represented
    leaf_coherent source r_slice r_bounds.1 far_r outside_vertices outside_empty empty_open
    pivot (by
      intro k ordered
      simpa only [heights k, heights pivot] using strict_after k ordered)
    source_order wall separator (by rw [heights pivot]; exact smaller_height.trans early)
  rw [heights pivot] at bound
  exact ⟨r_slice.lowerHeight, r_slice.lower_bounds, r_slice.lower_closed,
    r_slice.lower_radius, bound⟩

end Unfoldings.ConvexCap.SectorForest
