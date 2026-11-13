module

public import Unfoldings.Roof.DeepGeometricWaterfall
public import Unfoldings.Roof.CompletionOutwardForest
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Constructed waterfall strip interiors lie in the actual uncut completion domain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (T : K.CompletionMesh φ region extra)

theorem completionOutward_exists_regular_waterfall (positive : 0 < t) (small : t < 1)
    (cutoff : ℝ) (deep : Metric.closedBall origin cutoff ⊆ interior
      (SpatialEnvelope.clip (K.completionPlanes T.tentHeight (Real.sin φ / 2)) T.level)) :
    let L := T.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    let R := (M.completionOutwardForest T positive small).val
    ∀ i : FiveSector, ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
      ∀ S ∈ P.cells, ∀ z ∈ S.strictCarrier,
        z.re + z.im ∈ Set.Icc 0 cutoff →
          origin + (fiveSectorFrame t positive small i).place.symm z ∈
            L.cap.footprint \ L.cap.projectedCutSet R.retain := by
  let F := T.cornerTails M.inside
  let L := T.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  let R := (M.completionOutwardForest T positive small).val
  have covered := T.cornerTails_covers_rim M.inside
  refine fun i => ?_
  obtain ⟨P, regular⟩ := M.exists_deep_geometric_sector_waterfall F covered positive small
    i cutoff deep
  refine ⟨P, ?_⟩
  intro S cell z member height
  have physical := regular S cell z member height
  constructor
  · rw [L.cap_footprint]
    exact interior_subset physical.1
  · exact fun on_cut => physical.2 (R.projectedCutSet_subset on_cut)

end Unfoldings.ConvexRoof.SectorForest
