module

public import Unfoldings.Geometry.ChainPaths
public import Unfoldings.Geometry.SegmentEquation
public import Mathlib.Tactic.FinCases

/-! Explicit proper finite line constraints support an entire polygonal three-segment closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

def threeSegmentClosure (source c : Plane) : Set Plane :=
  Set.range P.path ∪ ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c source) ∪
    segment ℝ source (P.vertex 0))

/-- The extra initial-point equation retains even a chain with no genuine edge. -/
def closureEquations (source c : Plane) : Fin n ⊕ Fin 4 → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun i => segmentEquation (P.vertex i.castSucc) (P.vertex i.succ))
    ![segmentEquation (P.vertex 0) (P.vertex 0),
      segmentEquation (P.vertex (Fin.last n)) c, segmentEquation c source,
      segmentEquation source (P.vertex 0)]

theorem closureEquations_ne_zero (source c : Plane) (i : Fin n ⊕ Fin 4) :
    P.closureEquations source c i ≠ 0 := by
  cases i with
  | inl i => exact segmentEquation_ne_zero _ _
  | inr i => fin_cases i <;> exact segmentEquation_ne_zero _ _

/-- Every actual closure point lies on one of the constructed proper supporting equations. -/
theorem closureEquations_support (source c : Plane) (p : Plane)
    (member : p ∈ P.threeSegmentClosure source c) :
    ∃ i, P.closureEquations source c i p = 0 := by
  rcases member with in_path | ((first | second) | third)
  · have cover := P.path_range.subset in_path
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at cover
    rcases cover with root | ⟨i, t, rfl⟩
    · refine ⟨Sum.inr 0, ?_⟩
      rw [Set.mem_singleton_iff.mp root]
      exact segmentEquation_eq_zero (left_mem_segment ℝ _ _)
    · refine ⟨Sum.inl i, ?_⟩
      apply segmentEquation_eq_zero
      rw [segment_eq_image_lineMap]
      exact ⟨(t : ℝ), t.property, rfl⟩
  · exact ⟨Sum.inr 1, segmentEquation_eq_zero first⟩
  · exact ⟨Sum.inr 2, segmentEquation_eq_zero second⟩
  · exact ⟨Sum.inr 3, segmentEquation_eq_zero third⟩

end Unfoldings.PolygonalChain
