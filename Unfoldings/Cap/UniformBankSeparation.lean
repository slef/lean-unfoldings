module

public import Unfoldings.Cap.BankSegments

/-!
# A uniform geometric threshold for actual paired-seam noncrossing

The threshold and sector parameter precede the entire mesh. The actual forest,
quadrant calibration, and bank separation are constructed from geometric cap
input. No safe-bank or non-overlap certificate is required.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Uniformly small tilt separates each actual parent seam's banks up to flat contact. -/
theorem exists_uniform_sectorForest_parent_bank_separation {α : ℝ} (margin : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
        (K : ConvexCap C), AcuteMargin (C := C) α → K.TiltBound φ →
          (∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) →
          ∃ origin : C.Vertex Set.univ, ∃ M : K.SectorForest t origin,
            C.totalInteriorAngularDefect Set.univ < Real.pi ∧
              ∀ (D : FacewiseDevelopment C M.retain)
                (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) (s r : ℝ),
                s < 1 → r < 1 →
                  M.parentEntrancePoint D e s = M.parentExitPoint D e r →
                    s = r ∧ M.subtreeCurvature e.val = 0 := by
  obtain ⟨φ, bounds, t, tbounds, uniform⟩ := exists_uniform_sectorForest_sectorFrameData margin
  refine ⟨φ, bounds, t, tbounds, ?_⟩
  intro Face inst C K acute tilt internal
  obtain ⟨origin, M, budget, frames⟩ := uniform K acute tilt internal
  refine ⟨origin, M, budget, ?_⟩
  intro D e s r s_before r_before same
  obtain ⟨positive, small, ⟨B⟩⟩ := frames D
  exact ⟨B.bank_intersection_parameter_eq e s_before.le r_before.le budget.le same,
    B.parent_bank_contact_flat e s_before r_before budget same⟩

end Unfoldings.ConvexCap
