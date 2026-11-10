module

public import Unfoldings.Cap.SectorDevelopment
public import Unfoldings.Cap.UniformCurvature

/-! Choose forest and curvature thresholds together, uniformly before the entire input mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

theorem exists_uniform_sectorForest_curvature_lt {α ε : ℝ}
    (margin : 0 < α) (budget : 0 < ε) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          C.totalInteriorAngularDefect Set.univ < ε ∧
            ((∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
              ∃ origin : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ origin ∧
                Nonempty (K.SectorForest t origin)) := by
  obtain ⟨ψ, ψbounds, t, tbounds, forest⟩ := exists_uniform_tilt_sectorForest margin
  obtain ⟨χ, χbounds, curvature⟩ := exists_uniform_tilt_totalCurvature_lt budget
  let φ := min ψ χ
  have φpositive : 0 < φ := lt_min ψbounds.1 χbounds.1
  refine ⟨φ, ⟨φpositive, (min_le_left _ _).trans_lt ψbounds.2⟩, t, tbounds,
    fun K acute tilt => ?_⟩
  have forest_tilt := TiltBound.of_le K tilt φpositive.le
    (by linarith [ψbounds.2, Real.pi_pos]) (min_le_left _ _)
  have curvature_tilt := TiltBound.of_le K tilt φpositive.le
    (by linarith [χbounds.2, Real.pi_pos]) (min_le_right _ _)
  exact ⟨curvature K curvature_tilt, forest K acute forest_tilt⟩

end Unfoldings.ConvexCap
