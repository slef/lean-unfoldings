module

public import Unfoldings.Cap.ContourSourceOpeningBudget
public import Unfoldings.Geometry.PositiveOpeningMarginGap

/-! Complete source gaps from actual contour charges and a radially controlled reference bank. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexCap

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain selection))
  (starts : C.contourOriginalVertex selection Q 0 ∈ P.roots) (stage : Fin Q.length)

local notation "source" => C.contourOriginalVertex selection Q stage.castSucc
local notation "n" => P.distanceToRoot source

include K roots starts in
/-- The next positive source and its actual prior history construct a complete polygonal gap.
Only the reference bank's radial margins are input; the opening list and all budgets are derived. -/
theorem exists_contour_source_opening_gap
    (fresh : source ∉ (C.contourFrontier selection Q stage.castSucc).processed)
    (defect_positive : 0 < C.interiorAngularDefect Set.univ source)
    (bank : PolygonalRay ℂ n) (nonzero : bank.direction ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (curvature_budget : 3 * C.totalInteriorAngularDefect Set.univ < (γ : ℝ) ^ 2)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      (γ : ℝ) * (‖bank.chain.vertex i.castSucc - bank.chain.vertex j‖ * ‖bank.chain.edge i‖) ≤
        inner ℝ (bank.chain.vertex i.castSucc - bank.chain.vertex j) (bank.chain.edge i))
    (tail_margin : ∀ j : Fin (n + 1),
      (γ : ℝ) * (‖bank.chain.vertex (Fin.last n) - bank.chain.vertex j‖ * ‖bank.direction‖) ≤
        inner ℝ (bank.chain.vertex (Fin.last n) - bank.chain.vertex j) bank.direction) :
    let opened := bank.openings (C.contourRootwardOpenings selection Q stage.succ source)
    ∃ gap : Set ℂ,
      IsClosed gap ∧ frontier gap = bank.carrier ∪ opened.carrier ∧
      bank.carrier ∩ opened.carrier = {bank.start} ∧
      (interior gap).Nonempty ∧ closure (interior gap) = gap ∧
      CompleteSpace (PolygonalPoint gap) ∧ ContractibleSpace (PolygonalPoint gap) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        gap = ⋃ i, cells i := by
  let events : List (Opening n) := ⟨0, C.interiorAngularDefect Set.univ source⟩ ::
    C.contourRootwardOpenings selection Q stage.castSucc source
  have budget : openingBudget events ≤ C.totalInteriorAngularDefect Set.univ :=
    K.contour_source_opening_budget_le selection Q stage fresh
  have circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left budget (by norm_num)).trans_lt curvature_budget
  have positive_event (event : Opening n) (member : event ∈ events) : 0 < event.angle := by
    rcases List.mem_cons.mp member with same | old
    · subst event
      exact defect_positive
    · exact K.contourRootwardOpenings_positive selection Q stage.castSucc source event old
  let first : Fin events.length := ⟨0, by simp only [events, List.length_cons]; omega⟩
  have constructed := bank.exists_positive_opening_trace_gap_of_margin events nonzero γ positive
    small circle_budget margin tail_margin
    (fun k => positive_event events[k] (List.getElem_mem k.isLt)) first rfl rfl
  have same := C.contourRootwardOpenings_source_bank selection roots Q starts stage fresh bank
  simpa only [events, ← same] using constructed

end Unfoldings.ConvexCap
