module

public import Unfoldings.Cap.ExtendedWaterfallDomains
public import Unfoldings.Cap.RegularStripInjective
public import Unfoldings.Cap.ExtendedPathWedges

/-! Uniform injectivity on the constructed actual waterfall strip interiors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

/-- Every positive-width slab of every constructed strip has an injective actual developed map.
The tilt precedes both meshes. Continuity, chart selection, regular domains, and continued tails
are proved by construction, rather than supplied as geometric certificates. Global separation
between different developed strips remains a separate assertion. -/
theorem exists_uniform_extended_waterfall_injectivity :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C),
        K.TiltBound φ → ∀ {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin),
          ∀ (tpos : 0 < t) (tsmall : t < 1) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
            (source_height : 0 < K.roofHeight (K.projectedVertex origin))
            {Z : ℝ} (lower : Z < 0) (T : K.ClipSpatialTriangles Z),
              TriangleFamily.Conforming T.projectedTriangle →
                ∀ cutoff : ℝ, Metric.closedBall (K.projectedVertex origin) cutoff ⊆
                  interior (K.clipFootprint Z) →
                let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
                let F := T.cornerTails inside source_height lower
                let L := F.mesh T lower
                let Q := L.partition.normalizedCap L.conforming lower
                letI := @Fintype.ofFinite _ L.partition.finite
                let R := (M.cornerExtendedOutwardForest tpos tsmall T
                  internal source_height lower).val
                ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
                  ∃ calibration : Plane ≃ₗᵢ[ℝ] ℂ, ∀ i : FiveSector,
                    ∃ P : (fiveSectorFrame t tpos tsmall i).enclosingStrip.Subdivision,
                      ∀ S ∈ P.cells, ∀ a b : ℝ, 0 ≤ a → b ≤ cutoff →
                        (∀ h ∈ Set.Icc a b, S.lower.coordinate h < S.upper.coordinate h) →
                        Set.InjOn (D.centeredMap Q (K.projectedVertex origin) calibration
                          (fiveSectorFrame t tpos tsmall i).place)
                          {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc a b} := by
  obtain ⟨φ, bounds, normal, control⟩ := exists_uniform_regular_strip_injectivity.{0, 0}
  refine ⟨φ, bounds, ?_⟩
  intro Face _ C K tilt t origin M tpos tsmall internal source_height Z lower T conforming
    cutoff deep
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest tpos tsmall T internal source_height lower).val
  refine fun D => ?_
  have height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2 := fun f => normal.trans (tilt f)
  have wedges := M.cornerExtendedOutward_curvedPathWedges tpos tsmall T internal source_height
    lower conforming height
  have roof_tilt : Q.TiltBound φ := L.partition.normalizedCap_tiltBound L.conforming lower tilt
  obtain ⟨calibration, injective⟩ := control Q roof_tilt (K.projectedVertex origin)
    (M.extendedGeometricCuts F) R wedges D
  refine ⟨calibration, ?_⟩
  intro i
  obtain ⟨P, regular⟩ := M.cornerExtendedOutward_exists_regular_waterfall tpos tsmall T internal
    source_height lower cutoff deep i
  refine ⟨P, ?_⟩
  intro S cell a b nonnegative below width
  apply injective (fiveSectorFrame t tpos tsmall i).place S a b width
  intro z member slab
  exact regular S cell z member ⟨nonnegative.trans slab.1, slab.2.trans below⟩

end Unfoldings.ConvexCap
