module

public import Unfoldings.Cap.SupportedContourOpeningUpdate
public import Unfoldings.Cap.ContourSourceOpeningBudget
public import Unfoldings.Geometry.OpeningCast
public import Unfoldings.Geometry.TerminalEdgeOpeningGap

/-! Canonical source gaps retain every finite bank and its actual last-edge continuation. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexCap

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (Q : C.BoundaryContour (C.selectedRetain selection))
  (starts : C.contourOriginalVertex selection Q 0 ∈ P.roots) (stage : Fin Q.length)

local notation "source" => C.contourOriginalVertex selection Q stage.castSucc
local notation "n" => P.distanceToRoot source

include K roots starts in
/-- A positive fresh source gives its canonical next-history gap on the complete finite bank.
Tail margins, charges and event labels are derived, with unused isolated roots allowed. -/
theorem exists_sourceBank_opening_gap
    (fresh : source ∉ (C.contourFrontier selection Q stage.castSucc).processed)
    (defect_positive : 0 < C.interiorAngularDefect Set.univ source)
    (m : ℕ) (span : n = m + 1) (path : PolygonalChain ℂ (m + 1))
    (nonzero : path.edge (Fin.last m) ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (curvature_budget : 3 * C.totalInteriorAngularDefect Set.univ < (γ : ℝ) ^ 2)
    (margin : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), j.val ≤ i.val →
      (γ : ℝ) * (‖path.vertex i.castSucc - path.vertex j‖ * ‖path.edge i‖) ≤
        inner ℝ (path.vertex i.castSucc - path.vertex j) (path.edge i)) :
    let bank := path.terminalEdgeRay
    let opened := bank.openings
      (castOpenings span (C.contourRootwardOpenings selection Q stage.succ source))
    ∃ gap : Set ℂ,
      IsClosed gap ∧ frontier gap = bank.carrier ∪ opened.carrier ∧
      bank.carrier ∩ opened.carrier = {bank.start} ∧
      (interior gap).Nonempty ∧ closure (interior gap) = gap ∧
      CompleteSpace (PolygonalPoint gap) ∧ ContractibleSpace (PolygonalPoint gap) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        gap = ⋃ i, cells i := by
  let old := C.contourRootwardOpenings selection Q stage.castSucc source
  let events : List (Opening (m + 1)) :=
    ⟨0, C.interiorAngularDefect Set.univ source⟩ :: castOpenings span old
  have budget : openingBudget events ≤ C.totalInteriorAngularDefect Set.univ := by
    have original := K.contour_source_opening_budget_le selection Q stage fresh
    change |C.interiorAngularDefect Set.univ source| +
      openingBudget (castOpenings span old) ≤ _
    rw [castOpenings_budget]
    exact original
  have circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left budget (by norm_num)).trans_lt curvature_budget
  have angles (event : Opening (m + 1)) (member : event ∈ events) : 0 < event.angle := by
    rcases List.mem_cons.mp member with same | old_event
    · subst event
      exact defect_positive
    · exact castOpenings_positive span old
        (fun event present => K.contourRootwardOpenings_positive selection Q stage.castSucc
          source event present) event old_event
  let first : Fin events.length := ⟨0, by simp only [events, List.length_cons]; omega⟩
  have constructed := path.exists_terminalEdge_opening_gap events nonzero γ positive small
    circle_budget margin (fun k => angles events[k] (List.getElem_mem k.isLt)) first rfl rfl
  have original := C.contourRootwardOpenings_source_bank_of_boundary_roots selection roots Q
    starts stage fresh (path.terminalEdgeRay.cast span.symm)
  have same := congrArg (fun bank : PolygonalRay ℂ n => bank.cast span) original
  simp only [PolygonalRay.cast_openings, PolygonalRay.cast_cast, castOpenings_cons,
    Opening.cast_source] at same
  simpa only [events, old, ← same] using constructed

end Unfoldings.ConvexCap
