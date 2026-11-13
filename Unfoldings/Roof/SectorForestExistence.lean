module

public import Unfoldings.Roof.ForestSource
public import Unfoldings.Roof.SectorDevelopment

/-! Uniform existence of original-edge acute forests for arbitrary-rim roofs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Construct an interior-source forest, including roofs with no interior mesh vertices. -/
theorem exists_sectorForest {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (acute : ∀ i f j, ((K.projectedTriangle f).affineImage
      (threeSectorCoordinates t i).toAffineMap
        (threeSectorCoordinates_affine_injective nonnegative small i)).cornerAngle j <
          Real.pi / 2) :
    ∃ origin : Plane, Nonempty (K.SectorForest t origin) := by
  obtain ⟨origin, inside, maximal⟩ := K.exists_interior_forest_source
  exact ⟨origin, ⟨K.sectorForest nonnegative small origin inside
    (fun v internal => (maximal v internal).le) acute⟩⟩

/-- Tilt and sector width depend only on the acute margin, before any roof or mesh is supplied.
Boundary heights and the existence of interior vertices are unrestricted. -/
theorem exists_uniform_tilt_sectorForest {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ {Face' : Type u} [Fintype Face'] {C' : TriangleComplex.{u, v} Face'}
        (K : ConvexRoof C'), AcuteMargin (C := C') α → K.TiltBound φ →
          ∃ origin : Plane, Nonempty (K.SectorForest t origin) := by
  by_cases small : α < Real.pi / 2
  · obtain ⟨φ, φbounds, project⟩ := exists_uniform_acute_projection_tilt positive
    obtain ⟨t, tbounds, sectors⟩ := exists_threeSector_acute_triangles (half_pos positive)
      (by linarith [Real.pi_pos])
    refine ⟨φ, φbounds, t, tbounds, fun K acute tilt => ?_⟩
    apply K.exists_sectorForest tbounds.1.le (by linarith [tbounds.2])
    intro i f j
    exact sectors i (K.projectedTriangle f) (fun j => (project K acute tilt f j).le) j
  · refine ⟨Real.pi / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩,
      1 / 8, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro Face' inst C' K acute _
    exact (small (acuteMargin_lt_pi_div_two K acute)).elim

end Unfoldings.ConvexRoof
