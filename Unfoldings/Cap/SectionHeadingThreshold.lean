module

public import Unfoldings.Cap.SectionHeadingBound
public import Unfoldings.Cap.SectorThreshold

/-!
# A positive actual section-heading threshold before the entire mesh

The same numerical choice constructs the acute-sector original-edge forest and
makes twice the tilt plus twice actual total curvature arbitrarily small. The
threshold depends only on the acute margin and requested heading tolerance.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Forest construction and the actual section-heading budget use one mesh-independent threshold. -/
theorem exists_uniform_sectorForest_section_heading_lt {α ε : ℝ}
    (margin : 0 < α) (budget : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          2 * φ + 2 * C.totalInteriorAngularDefect Set.univ < ε ∧
            ((∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
              ∃ origin : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ origin ∧
                Nonempty (K.SectorForest t origin)) := by
  obtain ⟨ψ, ψbounds, t, tbounds, forest⟩ :=
    exists_uniform_sectorForest_curvature_lt margin (show 0 < ε / 8 by positivity)
  let φ := min ψ (ε / 8)
  have positive : 0 < φ := lt_min ψbounds.1 (by positivity)
  refine ⟨φ, ⟨positive, (min_le_left _ _).trans_lt ψbounds.2⟩, t, tbounds,
    fun K acute tilt => ?_⟩
  have relaxed := TiltBound.of_le K tilt positive.le
    (by linarith [ψbounds.2, Real.pi_pos]) (min_le_left _ _)
  obtain ⟨curvature, constructed⟩ := forest K acute relaxed
  have small : φ ≤ ε / 8 := min_le_right _ _
  exact ⟨by linarith, constructed⟩

end Unfoldings.ConvexCap
