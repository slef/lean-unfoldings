module

public import Unfoldings.Cap.ProcessedParentBankHeading
public import Unfoldings.Geometry.FrontierOpeningHistory
public import Unfoldings.Geometry.CanonicalAncestorOpenings

/-! Canonical source events recover actual parent-bank holonomy, including flat vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ) (frontier : P.ParentFrontier)
  {n : ℕ} (path : Fin (n + 1) → C.Vertex Set.univ) (sources : List (C.Vertex Set.univ))
  (reaches : ∀ source ∈ sources, ∃ i, P.Ancestor source (path i))

/-- Canonical openings measure the actual original intermediate bank, as an unreduced real phase.
Removing all flat charges preserves this equality exactly. -/
theorem ancestorOpenings_heading_eq_parentBankHeading
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j)) (distinct : sources.Nodup)
    (members : ∀ source, source ∈ sources ↔
      source ∈ frontier.processedDescendants (path (Fin.last n)))
    (i : Fin n) (nonroot : path i.castSucc ∉ P.roots)
    (processed : path i.castSucc ∈ frontier.processed) :
    openingHeading (withoutZeroOpenings
      (P.ancestorOpenings path (C.interiorAngularDefect Set.univ) sources reaches)) i =
      K.processedParentBankHeading selection roots frontier (path i.castSucc)
        nonroot processed := by
  rw [withoutZeroOpenings_heading,
    frontier.ancestorOpenings_heading_eq_processedWeight path _ sources reaches ordered distinct
      members i,
    K.processedParentBankHeading_eq]

include K in
/-- The canonical history spends at most total original curvature, with flat charges removed. -/
theorem ancestorOpenings_budget_le_totalCurvature (distinct : sources.Nodup) :
    openingBudget (withoutZeroOpenings
      (P.ancestorOpenings path (C.interiorAngularDefect Set.univ) sources reaches)) ≤
      C.totalInteriorAngularDefect Set.univ := by
  rw [withoutZeroOpenings_budget]
  exact P.ancestorOpenings_budget_le_total path _ sources reaches K.interiorCurvature_nonneg
    distinct

include K in
/-- Flat original vertices require no positive-curvature hypothesis or artificial opening. -/
theorem ancestorOpenings_positive_after_removing_flat
    (event : Opening n) (member : event ∈ withoutZeroOpenings
      (P.ancestorOpenings path (C.interiorAngularDefect Set.univ) sources reaches)) :
    0 < event.angle :=
  withoutZeroOpenings_positive _
    (P.ancestorOpenings_angles_nonnegative path _ sources reaches K.interiorCurvature_nonneg)
    event member

/-- The actual first-contact history constructs the opening list and all its coverage data. -/
theorem historyOpenings_heading_eq_parentBankHeading (seeds : List (C.Vertex Set.univ))
    (root : {v // v ∈ P.roots}) (last : path (Fin.last n) = root.val)
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j))
    (i : Fin n) (nonroot : path i.castSucc ∉ P.roots)
    (processed : path i.castSucc ∈ ((P.initialFrontier).run seeds).processed) :
    openingHeading (P.historyOpenings seeds root path last (C.interiorAngularDefect Set.univ)) i =
      K.processedParentBankHeading selection roots ((P.initialFrontier).run seeds)
        (path i.castSucc) nonroot processed := by
  rw [P.historyOpenings_heading seeds root path last _ ordered,
    K.processedParentBankHeading_eq]

include K in
/-- Repeated seeds and flat vertices preserve the original total curvature budget. -/
theorem historyOpenings_budget_le_totalCurvature (seeds : List (C.Vertex Set.univ))
    (root : {v // v ∈ P.roots}) (last : path (Fin.last n) = root.val) :
    openingBudget (P.historyOpenings seeds root path last (C.interiorAngularDefect Set.univ)) ≤
      C.totalInteriorAngularDefect Set.univ :=
  P.historyOpenings_budget_le_total seeds root path last _ K.interiorCurvature_nonneg

end Unfoldings.ConvexCap
