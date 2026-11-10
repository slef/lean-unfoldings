module

public import Unfoldings.Cap.SectorForest

/-! Construct the sector forest uniformly from an internal horizontal extremum. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem exists_sectorForest {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (acute : ∀ i f j, ((K.projectedTriangle f).affineImage
      (threeSectorCoordinates t i).toAffineMap
        (threeSectorCoordinates_affine_injective nonnegative small i)).cornerAngle j < Real.pi / 2)
    (nonempty : ∃ v : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ v) :
    ∃ origin : C.Vertex Set.univ, ¬ C.IsBoundaryVertex Set.univ origin ∧
      Nonempty (K.SectorForest t origin) := by
  classical
  let vertices := Finset.univ.filter (fun v : C.Vertex Set.univ => ¬ C.IsBoundaryVertex Set.univ v)
  have present : vertices.Nonempty := by
    obtain ⟨v, hv⟩ := nonempty
    exact ⟨v, by simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv⟩
  obtain ⟨q, hq, maximal⟩ := vertices.exists_max_image (fun v => K.projectedVertex v 0) present
  have interior : ¬ C.IsBoundaryVertex Set.univ q := (Finset.mem_filter.mp hq).2
  have bound (v : C.Vertex Set.univ) (internal : ¬ C.IsBoundaryVertex Set.univ v) :
      K.projectedVertex v 0 ≤ K.projectedVertex q 0 :=
    maximal v (by
      simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact internal)
  exact ⟨q, interior, ⟨K.sectorForest nonnegative small q bound acute⟩⟩

/-- Tilt and sector width are chosen before the face type, mesh, cap, and source. -/
theorem exists_uniform_tilt_sectorForest {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexCap C'), AcuteMargin (C := C') α → K.TiltBound φ →
          (∃ v : C'.Vertex Set.univ, ¬ C'.IsBoundaryVertex Set.univ v) →
            ∃ origin : C'.Vertex Set.univ, ¬ C'.IsBoundaryVertex Set.univ origin ∧
              Nonempty (K.SectorForest t origin) := by
  by_cases small : α < Real.pi / 2
  · obtain ⟨φ, φbounds, project⟩ := exists_uniform_acute_projection_tilt positive
    obtain ⟨t, tbounds, sectors⟩ := exists_threeSector_acute_triangles (half_pos positive)
      (by linarith [Real.pi_pos])
    refine ⟨φ, φbounds, t, tbounds, fun K acute tilt nonempty => ?_⟩
    apply K.exists_sectorForest tbounds.1.le (by linarith [tbounds.2]) _ nonempty
    intro i f j
    exact sectors i (K.projectedTriangle f) (fun j => (project K acute tilt f j).le) j
  · refine ⟨Real.pi / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩,
      1 / 8, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro Face' inst C' K acute _ _
    exact (small (acuteMargin_lt_pi_div_two K acute)).elim

end Unfoldings.ConvexCap
