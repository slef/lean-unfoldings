module

public import Unfoldings.Roof.SharpOriginalBankHeading
public import Unfoldings.Roof.CompletionAcuteBankBudget
public import Unfoldings.Roof.CompletionLinearBankProgress
public import Unfoldings.Cap.AcuteJordanBankSide
public import Unfoldings.Geometry.TwoLinkClosureAlignment
public import Unfoldings.Geometry.GenericEndTrimming

/-! The sharp two-link turn bound for the actual selected side of an original acute bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

local instance acuteBankIndexFintype {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
    {I : Type u} {extra : I → Plane →ᵃ[ℝ] ℝ} (E : K.CompletionMesh φ region extra) :
    Fintype E.mesh.Index := @Fintype.ofFinite _ E.mesh.finite

/-- Changing these geometric presentations does not change the actual contour sum. -/
private theorem acute_budget_transport {Face : Type u} [Fintype Face]
    {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
    {J J' bank bank' : Set Plane} {corners corners' : Finset Plane}
    (curve : J' = J) (trace : bank' = bank) (ends : corners' = corners)
    (jordan : Schoenflies.IsJordanCurve J) (jordan' : Schoenflies.IsJordanCurve J')
    (inside : J ⊆ K.footprint) (inside' : J' ⊆ K.footprint)
    (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)
    (avoids' : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J') {budget : ℝ}
    (bound : |∑ i ∈ K.jordanGeometricBankIndices jordan inside avoids bank corners,
      K.jordanContourTurnError jordan inside avoids i| ≤ budget) :
    |∑ i ∈ K.jordanGeometricBankIndices jordan' inside' avoids' bank' corners',
      K.jordanContourTurnError jordan' inside' avoids' i| ≤ budget := by
  subst J' bank' corners'
  exact bound

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

set_option maxHeartbeats 1400000 in
open Classical in
/-- Strict progress in the two diagonal controls constructs a regular closing
disk for the specified original bank and bounds its untrimmed real heading error. -/
theorem abs_projectedMetricHeadingError_le_sharp_of_acute_controls
    {φ : ℝ} (positive : 0 < φ) (small_tilt : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    {retain : Set C.Seam} {n : ℕ} (coarse : (C.boundarySystem retain).Chain (n + 1))
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (coarse.point i).val))
    (source : Plane) (radial : (K.folding.projectedBoundaryChain coarse).RadialFrom source 0)
    (h k : Plane →L[ℝ] ℝ) (joint : Function.Bijective fun p => (h p, k p))
    (first : ∀ i, 0 < h ((K.folding.projectedBoundaryChain coarse).edge i))
    (last : ∀ i, 0 < k ((K.folding.projectedBoundaryChain coarse).edge i)) :
    |K.projectedMetricHeadingError coarse (Fin.last (n + 1))| ≤ acuteConeDevelopmentHeading φ := by
  let P := K.folding.projectedBoundaryChain coarse
  obtain ⟨region, compact, convex, bank_inside, feasible⟩ :=
    P.exists_compact_twoLink_comparison_region h k first last joint
  let oldEq : ULift.{u} (Fin (n + 2) ⊕ Fin 4) → Plane →ᵃ[ℝ] ℝ :=
    fun i => P.closureEquations (P.vertex 0) (P.vertex 0) i.down
  have oldProper (i) : oldEq i ≠ 0 := P.closureEquations_ne_zero _ _ i.down
  obtain ⟨E₀⟩ := K.exists_completionMesh positive small_tilt compact oldEq oldProper
  let point (i : E₀.mesh.Index × Fin 3) := (E₀.mesh.projectedTriangle i.1).vertex i.2
  let : Finite E₀.mesh.Index := E₀.mesh.finite
  obtain ⟨a, b, trim_a, trim_b, trim_avoids⟩ :=
    P.exists_generic_trimEnds point
      (K.projectedBoundaryChain_edge_ne_zero coarse 0)
      (K.projectedBoundaryChain_edge_ne_zero coarse (Fin.last (n + 1)))
  let Q := P.trimEnds a b
  have h_progress := P.trimEnds_positive_linear_edges a b trim_a.2 trim_b.1 h first
  have k_progress := P.trimEnds_positive_linear_edges a b trim_a.2 trim_b.1 k last
  have bank : Set.range Q.path ⊆ interior region := (P.trimEnds_path_subset a b).trans bank_inside
  obtain ⟨low_open, high_open⟩ := feasible
    (Q.vertex 0) (P.trimEnds_path_subset a b (Q.vertex_mem_path_range 0))
    (Q.vertex (Fin.last (n + 2)))
      (P.trimEnds_path_subset a b (Q.vertex_mem_path_range (Fin.last (n + 2))))
  obtain ⟨low, low_first, low_last, low_in, low_jordan, low_regular, low_links⟩ :=
    Q.exists_regular_twoLink_closure_in_region h k h_progress k_progress (by omega)
      convex bank low_open point E₀.oldEdgeEquation E₀.oldEdgeEquation_ne_zero
      (fun i => (trim_avoids i).1) (fun i => (trim_avoids i).2)
  obtain ⟨high, high_first, high_last, high_in, high_jordan, high_regular, high_links⟩ :=
    Q.exists_regular_twoLink_closure_in_region k h k_progress h_progress (by omega)
      convex bank high_open point E₀.oldEdgeEquation E₀.oldEdgeEquation_ne_zero
      (fun i => (trim_avoids i).1) (fun i => (trim_avoids i).2)
  let start := Q.vertex 0
  let leftEq : ULift.{u} ((Fin (n + 2) ⊕ Fin 4) ⊕ (Fin 4 × Fin 2)) → Plane →ᵃ[ℝ] ℝ := Q.markedClosureEquations start low
  let rightEq : ULift.{u} ((Fin (n + 2) ⊕ Fin 4) ⊕ (Fin 4 × Fin 2)) → Plane →ᵃ[ℝ] ℝ := Q.markedClosureEquations start high
  let equations := Sum.elim leftEq rightEq
  have proper : ∀ i, equations i ≠ 0 := Sum.rec (Q.markedClosureEquations_ne_zero start low)
    (Q.markedClosureEquations_ne_zero start high)
  let eq := K.combinedCompletionEquations equations
  let eq_proper := K.combinedCompletionEquations_ne_zero equations proper
  let L := E₀.alignToLines eq eq_proper
  have tilt_L := L.cap_tilt positive small_tilt tilt
  have heights := fun i => height_bound.trans (K.completionPlanes_tilt positive small_tilt tilt E₀.tentHeight i)
  have bank_avoids (f : E₀.mesh.Index) :
      Disjoint (interior (E₀.mesh.projectedTriangle f).carrier) (Set.range Q.path) := by
    apply E₀.mesh.interior_avoids_supported_curve oldProper _ f
    intro p member
    obtain ⟨i, equal⟩ := P.closureEquations_support (P.vertex 0) (P.vertex 0) p
      (Or.inl (P.trimEnds_path_subset a b member))
    exact ⟨ULift.up i, equal⟩
  have low_corners := E₀.regular_acute_closing_corners Q low h k h_progress k_progress
    low_first.le low_last.le (low_in.trans interior_subset) bank_avoids
    (fun f i => trim_avoids (f, i))
    (fun f i edge => low_regular (f, i) (segmentEquation_eq_zero edge))
  have high_corners := E₀.regular_acute_closing_corners Q high k h k_progress h_progress
    high_first.le high_last.le (high_in.trans interior_subset) bank_avoids
    (fun f i => trim_avoids (f, i))
    (fun f i edge => high_regular (f, i) (segmentEquation_eq_zero edge))
  have inside_low : Q.twoLinkClosure low ⊆ interior L.cap.footprint :=
    (low_in.trans interior_subset).trans L.region_inside
  have inside_high : Q.twoLinkClosure high ⊆ interior L.cap.footprint :=
    (high_in.trans interior_subset).trans L.region_inside
  have avoids_low := L.cap_avoids_supported_curve eq_proper
    (fun p (member : p ∈ Q.twoLinkClosure low) => by
      rw [← Q.threeSegmentClosure_of_initial_eq_twoLinkClosure low] at member
      obtain ⟨i, equal⟩ := Q.markedClosureEquations_support start low p member
      exact ⟨.inr (.inl i), equal⟩)
  have avoids_high := L.cap_avoids_supported_curve eq_proper
    (fun p (member : p ∈ Q.twoLinkClosure high) => by
      rw [← Q.threeSegmentClosure_of_initial_eq_twoLinkClosure high] at member
      obtain ⟨i, equal⟩ := Q.markedClosureEquations_support start high p member
      exact ⟨.inr (.inr i), equal⟩)
  have budget_low := E₀.alignToLines_acute_bank_bound eq eq_proper Q low h k
    h_progress k_progress low_first low_last positive.le small_tilt heights
    low_corners (fun j t f i => low_links j t (f, i)) tilt_L low_jordan inside_low avoids_low
  have budget_high := E₀.alignToLines_acute_bank_bound eq eq_proper Q high k h
    k_progress h_progress high_first high_last positive.le small_tilt heights
    high_corners (fun j t f i => high_links j t (f, i)) tilt_L high_jordan inside_high avoids_high
  have jordan_marked : Schoenflies.IsJordanCurve (Q.threeSegmentClosure start low) := by
    rw [Q.threeSegmentClosure_of_initial_eq_twoLinkClosure low]
    exact low_jordan
  have filling : PlanarTopology.closedJordanDomain (Q.threeSegmentClosure start low) ⊆ region :=
    PlanarTopology.closedJordanDomain_subset_convex jordan_marked compact convex
      (by rw [Q.threeSegmentClosure_of_initial_eq_twoLinkClosure low]
          exact low_in.trans interior_subset)
  let leftView := L.selectConstraints (K.combinedCompletionEquations leftEq)
    (Sum.elim Sum.inl (fun i => Sum.inr (Sum.inl i))) (fun i => by cases i <;> rfl)
  let E := leftView.restrictRegion filling
  let V := E.originalConstraintView
  let W := CompletionMesh.markedOriginalBankWindow coarse cut a b start low
    trim_a.2 trim_b.2 jordan_marked E
  let P' := V.cap.projectedBoundaryChain V.originalPieceSet W.chain
  have trace : Set.range P'.path = Set.range Q.path := W.cap_projected_trace_eq_trim source radial
  have head : P'.vertex 0 = Q.vertex 0 :=
    W.cap_projected_initial.trans (P.trimEnds_start a b).symm
  have tail : P'.vertex (Fin.last (W.length + 1)) = Q.vertex (Fin.last (n + 2)) :=
    W.cap_projected_terminal.trans (P.trimEnds_last a b).symm
  have curve (c : Plane) : P'.twoLinkClosure c = Q.twoLinkClosure c := by
    unfold PolygonalChain.twoLinkClosure
    rw [trace, head, tail]
  have corners (c : Plane) : P'.twoClosingCorners c = Q.twoClosingCorners c := by
    simp only [PolygonalChain.twoClosingCorners, head, tail]
  have inside' (c : Plane) (inside : Q.twoLinkClosure c ⊆ interior L.cap.footprint) :
      P'.twoLinkClosure c ⊆ interior V.cap.footprint := (curve c).subset.trans inside
  have avoids' (c : Plane)
      (avoids : ∀ f, Disjoint (interior (L.cap.projectedTriangle f).carrier) (Q.twoLinkClosure c)) :
      ∀ f, Disjoint (interior (V.cap.projectedTriangle f).carrier) (P'.twoLinkClosure c) :=
    fun f => (avoids f).mono_right (curve c).subset
  have jf (c : Plane) (jordan : Schoenflies.IsJordanCurve (Q.twoLinkClosure c)) :
      Schoenflies.IsJordanCurve (P'.twoLinkClosure c) := (curve c).symm ▸ jordan
  have h_fine (i : Fin (W.length + 1)) : 0 < h (P'.edge i) :=
    W.cap_projected_edge_progress h first i
  have k_fine (i : Fin (W.length + 1)) : 0 < k (P'.edge i) :=
    W.cap_projected_edge_progress k last i
  have low_first' : h low < h (P'.vertex 0) := by rwa [head]
  have low_last' : k (P'.vertex (Fin.last (W.length + 1))) < k low := by rwa [tail]
  have high_first' : k high < k (P'.vertex 0) := by rwa [head]
  have high_last' : h (P'.vertex (Fin.last (W.length + 1))) < h high := by rwa [tail]
  have excluded := V.cap.not_mem_mate_face_of_one_acute_closure V.originalPieceSet W.chain h k
    h_fine k_fine joint.injective low high low_first'.le low_last'.le high_first'.le high_last'.le
    (jf low low_jordan) (jf high high_jordan) (avoids' low avoids_low) (avoids' high avoids_high)
  have bound : |∑ i : Fin W.length, V.cap.cutBoundaryTurnError V.originalPieceSet (W.chain.point i.succ)| ≤
      acuteConeDevelopmentHeading φ := by
    rcases excluded with low_out | high_out
    · apply V.cap.abs_sum_acute_original_bank_turn_error_le V.originalPieceSet W.chain low h k
        h_fine k_fine low_first' low_last'.le (jf low low_jordan) (inside' low inside_low)
        (avoids' low avoids_low) low_out
      exact acute_budget_transport V.cap (curve low) trace (corners low) low_jordan
        (jf low low_jordan) (inside_low.trans interior_subset)
        ((inside' low inside_low).trans interior_subset) avoids_low (avoids' low avoids_low) budget_low
    · apply V.cap.abs_sum_acute_original_bank_turn_error_le V.originalPieceSet W.chain high k h
        k_fine h_fine high_first' high_last'.le (jf high high_jordan) (inside' high inside_high)
        (avoids' high avoids_high) high_out
      exact acute_budget_transport V.cap (curve high) trace (corners high) high_jordan
        (jf high high_jordan) (inside_high.trans interior_subset)
        ((inside' high inside_high).trans interior_subset) avoids_high (avoids' high avoids_high) budget_high
  let roll := V.cap.boundaryChainRollHeading_sub_projectedFanRollHeading_last
    V.originalPieceSet W.chain
  exact (congrArg abs ((W.terminal_real_error_eq trim_b.1).symm.trans roll)).le.trans bound

end Unfoldings.ConvexRoof
