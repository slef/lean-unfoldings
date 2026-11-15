module

public import Unfoldings.Cap.Topology
public import Unfoldings.Cap.CurvatureBudget
public import Unfoldings.Cap.RimAngles
public import Unfoldings.Complex.ProcessedSubtreeRolling
public import Unfoldings.Topology.ProcessedDescendantWeights

/-! Actual intermediate parent-bank headings and exact singleton curvature increments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (frontier : P.ParentFrontier) (vertex : C.Vertex Set.univ)
  (nonroot : vertex ∉ P.roots) (processed : vertex ∈ frontier.processed)

/-- Measure the unreduced reversed-exit heading on the actual intermediate cut contour.
Both banks and their contour are constructed; no current development is assumed. -/
def processedParentBankHeading : ℝ :=
  let Q := K.folding.processedParentBoundaryContour S roots frontier K.diskHomeomorph
  let banks := C.exists_processed_subtree_real_bank_heading S frontier roots Q
    vertex nonroot processed
  C.boundaryRollHeading (Q.rotate C banks.choose) banks.choose_spec.choose + Real.pi

/-- The actual current bank measurement equals exactly the processed original curvature. -/
theorem processedParentBankHeading_eq :
    K.processedParentBankHeading S roots frontier vertex nonroot processed =
      frontier.processedDescendantWeight (C.interiorAngularDefect Set.univ) vertex := by
  let Q := K.folding.processedParentBoundaryContour S roots frontier K.diskHomeomorph
  let banks := C.exists_processed_subtree_real_bank_heading S frontier roots Q
    vertex nonroot processed
  exact banks.choose_spec.choose_spec.choose_spec.2.2

/-- Every intermediate measurement lies within the original total-curvature budget. -/
theorem processedParentBankHeading_bounds :
    0 ≤ K.processedParentBankHeading S roots frontier vertex nonroot processed ∧
      K.processedParentBankHeading S roots frontier vertex nonroot processed ≤
        C.totalInteriorAngularDefect Set.univ := by
  rw [K.processedParentBankHeading_eq S roots frontier vertex nonroot processed]
  exact ⟨Finset.sum_nonneg (fun w _ => K.interiorCurvature_nonneg w),
    K.sum_interiorAngularDefect_le_totalCurvature (frontier.processedDescendants vertex)⟩

open Classical in
/-- Comparing actual bank measurements before and after a singleton cut charges just the
new original source, precisely on the ancestor subtrees containing that source. -/
theorem processedParentBankHeading_single_step (seed : C.Vertex Set.univ)
    (fresh : seed ∉ frontier.processed) (single : frontier.contactTime seed = 1) :
    K.processedParentBankHeading S roots (frontier.process seed) vertex nonroot (Or.inl processed) =
      K.processedParentBankHeading S roots frontier vertex nonroot processed +
        (if P.Ancestor seed vertex then C.interiorAngularDefect Set.univ seed else 0) := by
  calc
    _ = (frontier.process seed).processedDescendantWeight
        (C.interiorAngularDefect Set.univ) vertex :=
      K.processedParentBankHeading_eq S roots (frontier.process seed) vertex nonroot
        (Or.inl processed)
    _ = _ := by
      rw [K.processedParentBankHeading_eq S roots frontier vertex nonroot processed]
      exact frontier.processedDescendantWeight_single_step (C.interiorAngularDefect Set.univ)
        vertex seed fresh single

/-- Zero-curvature sources cause zero change; no positive-curvature premise is required. -/
theorem abs_processedParentBankHeading_single_step_le (seed : C.Vertex Set.univ)
    (fresh : seed ∉ frontier.processed) (single : frontier.contactTime seed = 1) :
    |K.processedParentBankHeading S roots (frontier.process seed) vertex nonroot
        (Or.inl processed) -
      K.processedParentBankHeading S roots frontier vertex nonroot processed| ≤
        C.interiorAngularDefect Set.univ seed := by
  rw [K.processedParentBankHeading_single_step S roots frontier vertex nonroot processed
    seed fresh single, add_sub_cancel_left]
  split_ifs
  · exact (abs_of_nonneg (K.interiorCurvature_nonneg seed)).le
  · simpa only [abs_zero] using K.interiorCurvature_nonneg seed

end Unfoldings.ConvexCap
