module

public import Unfoldings.Geometry.VertexAvoidingWedgeClosure
public import Unfoldings.Geometry.SegmentLineAvoidance

/-! Generic vertex-avoiding Jordan closures retain actual radial support and outward geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane n)

/-- Construct actual generic closing links together with the supporting linear height,
strict radial progress and outward terminal link required by physical bank comparison. -/
theorem exists_supported_vertex_avoiding_wedge_closure {ι κ : Type*} [Finite ι] [Finite κ]
    (source : Plane) (strict : source ∈ P.strictRadialSources)
    (initial : 0 < dist source (P.vertex 0))
    (progress : dist source (P.vertex 0) < dist source (P.vertex (Fin.last n)))
    (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane)
    (inside : ∀ j, 0 ≤ (frame.symm (P.vertex j - source)).1 ∧
      0 ≤ (frame.symm (P.vertex j - source)).2)
    (point : ι → Plane) (equation : κ → Plane →ᵃ[ℝ] ℝ) (proper : ∀ i, equation i ≠ 0)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ (q c : Plane) (height : Plane →ₗ[ℝ] ℝ),
      dist q source < δ ∧ P.RadialFrom q 0 ∧
      0 < dist q (P.vertex 0) ∧ dist q (P.vertex 0) < dist q (P.vertex (Fin.last n)) ∧
      (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 ∧
      0 < inner ℝ (P.vertex (Fin.last n) - q) (c - P.vertex (Fin.last n)) ∧
      (∀ i, equation i q ≠ 0 ∧ equation i c ≠ 0) ∧
      (∀ i, q ≠ point i ∧ c ≠ point i) ∧
      (∀ i, point i ∈ segment ℝ (P.vertex 0) q → point i = P.vertex 0) ∧
      (∀ i, point i ∉ segment ℝ q c) ∧
      (∀ i, point i ∈ segment ℝ (P.vertex (Fin.last n)) c → point i = P.vertex (Fin.last n)) ∧
      Schoenflies.IsJordanCurve (Set.range P.path ∪
        ((segment ℝ (P.vertex (Fin.last n)) c ∪ segment ℝ c q) ∪
          segment ℝ q (P.vertex 0))) := by
  let sourceEquations : κ ⊕ ι → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim equation (fun i => segmentEquation (P.vertex 0) (point i))
  have source_proper (i : κ ⊕ ι) : sourceEquations i ≠ 0 := by
    cases i with
    | inl i => exact proper i
    | inr i => exact segmentEquation_ne_zero _ _
  obtain ⟨q, close, radial, first, last, wedge, regular_q⟩ := P.exists_generic_radial_source
    source strict initial progress frame inside sourceEquations source_proper positive
  have supported (z : Plane) (member : z ∈ Set.range P.path) :
      0 ≤ (frame.symm (z - q)).1 ∧ 0 ≤ (frame.symm (z - q)).2 := by
    constructor
    · exact P.height_nonneg_on_path q ((LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap)
        (fun j => (wedge j).1.le) member
    · exact P.height_nonneg_on_path q ((LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap)
        (fun j => (wedge j).2.le) member
  let closingEquations : κ ⊕ (ι ⊕ ι) → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim equation (Sum.elim (fun i => segmentEquation q (point i))
      (fun i => segmentEquation (P.vertex (Fin.last n)) (point i)))
  have closing_proper (i : κ ⊕ (ι ⊕ ι)) : closingEquations i ≠ 0 := by
    rcases i with i | (i | i)
    · exact proper i
    · exact segmentEquation_ne_zero _ _
    · exact segmentEquation_ne_zero _ _
  obtain ⟨c, regular_c, excluded, outward, jordan⟩ :=
    P.exists_generic_radial_wedge_closure q radial first last frame supported closingEquations
      closing_proper
  have q_regular (i : ι) : segmentEquation (P.vertex 0) (point i) q ≠ 0 :=
    regular_q (Sum.inr i)
  have q_different (i : ι) : q ≠ point i := ne_of_segmentEquation_ne_zero (q_regular i)
  have first_regular (i : ι) : segmentEquation q (point i) c ≠ 0 :=
    regular_c (Sum.inr (Sum.inl i))
  have last_regular (i : ι) : segmentEquation (P.vertex (Fin.last n)) (point i) c ≠ 0 :=
    regular_c (Sum.inr (Sum.inr i))
  have supporting_height : ∃ height : Plane →ₗ[ℝ] ℝ,
      (∀ z ∈ Set.range P.path, 0 ≤ height (z - q)) ∧ height (c - q) < 0 := by
    rcases excluded with left | right
    · refine ⟨(LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap, ?_, left⟩
      intro z member
      exact (supported z member).1
    · refine ⟨(LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap, ?_, right⟩
      intro z member
      exact (supported z member).2
  obtain ⟨height, supported_height, negative⟩ := supporting_height
  refine ⟨q, c, height, close, radial, first, last, supported_height, negative, outward,
    fun i => ⟨regular_q (Sum.inl i), regular_c (Sum.inl i)⟩,
    fun i => ⟨q_different i, ne_of_segmentEquation_ne_zero (first_regular i)⟩,
    fun i member => eq_endpoint_of_mem_segment_of_segmentEquation_ne_zero (q_regular i) member,
    ?_, fun i member => eq_endpoint_of_mem_segment_of_segmentEquation_ne_zero
      (last_regular i) member, jordan⟩
  intro i member
  exact (q_different i) (eq_endpoint_of_mem_segment_of_segmentEquation_ne_zero
    (first_regular i) member).symm

end Unfoldings.PolygonalChain
