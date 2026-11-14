module

public import Unfoldings.Geometry.StrictRadialTrimming
public import Unfoldings.Geometry.GenericEndTrimming
public import Unfoldings.Geometry.VertexAvoidingWedgeClosure
public import Unfoldings.Geometry.PolygonalClosureEquations
public import Unfoldings.Geometry.SegmentExtendedAvoidance

/-!
# Construct a fully regular three-link closure of an actual bank portion

Trimming preserves every original turn. The new source stays arbitrarily close
to the old source. All three complete closing lines avoid the prescribed
vertices, so the existing regular section-trace API applies to their crossings.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain Plane (n + 2))

/-- All generic incidences are constructed from actual bank geometry and finite exceptional data. -/
theorem exists_generic_bank_closure {ι κ : Type*} [Finite ι] [Finite κ]
    (source : Plane) (strict : source ∈ P.strictRadialSources)
    (initial : 0 < dist source (P.vertex 0))
    (first_nonzero : P.edge 0 ≠ 0) (last_nonzero : P.edge (Fin.last (n + 1)) ≠ 0)
    (frame : (ℝ × ℝ) ≃ₗ[ℝ] Plane)
    (inside : ∀ z ∈ Set.range P.path,
      0 ≤ (frame.symm (z - source)).1 ∧ 0 ≤ (frame.symm (z - source)).2)
    (point : ι → Plane) (equation : κ → Plane →ᵃ[ℝ] ℝ) (proper : ∀ i, equation i ≠ 0)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ a b : unitInterval, (0 < (a : ℝ) ∧ (a : ℝ) < 1) ∧
      (0 < (b : ℝ) ∧ (b : ℝ) < 1) ∧
      ∃ q c : Plane, dist q source < δ ∧ (P.trimEnds a b).RadialFrom q 0 ∧
        (∀ i, equation i q ≠ 0 ∧ equation i c ≠ 0) ∧
        (∀ i, q ≠ point i ∧ c ≠ point i) ∧
        (∀ i, ∀ t : ℝ,
          AffineMap.lineMap ((P.trimEnds a b).vertex 0) q t ≠ point i ∧
          AffineMap.lineMap q c t ≠ point i ∧
          AffineMap.lineMap ((P.trimEnds a b).vertex (Fin.last (n + 2))) c t ≠ point i) ∧
        Schoenflies.IsJordanCurve ((P.trimEnds a b).threeSegmentClosure q c) := by
  obtain ⟨a, b, first, last, endpoints⟩ :=
    P.exists_generic_trimEnds point first_nonzero last_nonzero
  let Q := P.trimEnds a b
  have radial := P.radialFrom_of_strictRadialSource strict
  have Q_strict : source ∈ Q.strictRadialSources :=
    P.strictRadialSource_trimEnds strict a b first.2 last.1
  have Q_initial : 0 < dist source (Q.vertex 0) := initial.trans_le
    (P.path_radius_bounds source radial (P.trimEnds_path_subset a b (Q.vertex_mem_path_range 0))).1
  have Q_progress := P.trimEnds_radius_progress a b radial last_nonzero last.1
  have Q_inside (j : Fin (n + 3)) : 0 ≤ (frame.symm (Q.vertex j - source)).1 ∧
      0 ≤ (frame.symm (Q.vertex j - source)).2 :=
    inside _ (P.trimEnds_path_subset a b (Q.vertex_mem_path_range j))
  let sourceEquations : κ ⊕ ι → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim equation (fun i => segmentEquation (Q.vertex 0) (point i))
  have source_proper (i : κ ⊕ ι) : sourceEquations i ≠ 0 := by
    cases i with
    | inl i => exact proper i
    | inr i => exact segmentEquation_ne_zero _ _
  obtain ⟨q, close, q_radial, q_initial, q_progress, wedge, q_regular⟩ :=
    Q.exists_generic_radial_source source Q_strict Q_initial Q_progress frame Q_inside
      sourceEquations source_proper positive
  have supported (z : Plane) (member : z ∈ Set.range Q.path) :
      0 ≤ (frame.symm (z - q)).1 ∧ 0 ≤ (frame.symm (z - q)).2 :=
    ⟨Q.height_nonneg_on_path q ((LinearMap.fst ℝ ℝ ℝ).comp frame.symm.toLinearMap)
      (fun j => (wedge j).1.le) member,
     Q.height_nonneg_on_path q ((LinearMap.snd ℝ ℝ ℝ).comp frame.symm.toLinearMap)
      (fun j => (wedge j).2.le) member⟩
  let closingEquations : κ ⊕ (ι ⊕ ι) → Plane →ᵃ[ℝ] ℝ :=
    Sum.elim equation (Sum.elim (fun i => segmentEquation q (point i))
      (fun i => segmentEquation (Q.vertex (Fin.last (n + 2))) (point i)))
  have closing_proper (i : κ ⊕ (ι ⊕ ι)) : closingEquations i ≠ 0 := by
    rcases i with i | (i | i)
    · exact proper i
    · exact segmentEquation_ne_zero _ _
    · exact segmentEquation_ne_zero _ _
  obtain ⟨c, c_regular, _, _, jordan⟩ := Q.exists_generic_radial_wedge_closure q q_radial
    q_initial q_progress frame supported closingEquations closing_proper
  have source_regular (i : ι) : segmentEquation (Q.vertex 0) (point i) q ≠ 0 :=
    q_regular (Sum.inr i)
  have middle_regular (i : ι) : segmentEquation q (point i) c ≠ 0 :=
    c_regular (Sum.inr (Sum.inl i))
  have terminal_regular (i : ι) : segmentEquation (Q.vertex (Fin.last (n + 2))) (point i) c ≠ 0 :=
    c_regular (Sum.inr (Sum.inr i))
  have different (i : ι) : q ≠ point i := ne_of_segmentEquation_ne_zero (source_regular i)
  exact ⟨a, b, first, last, q, c, close, q_radial,
    fun i => ⟨q_regular (Sum.inl i), c_regular (Sum.inl i)⟩,
    fun i => ⟨different i, ne_of_segmentEquation_ne_zero (middle_regular i)⟩,
    fun i t => ⟨lineMap_ne_of_segmentEquation_ne_zero (source_regular i) (endpoints i).1 t,
      lineMap_ne_of_segmentEquation_ne_zero (middle_regular i) (different i) t,
      lineMap_ne_of_segmentEquation_ne_zero (terminal_regular i) (endpoints i).2 t⟩, jordan⟩

end Unfoldings.PolygonalChain
