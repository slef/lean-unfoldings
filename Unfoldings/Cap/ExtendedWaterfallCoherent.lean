module

public import Unfoldings.Cap.ExtendedWaterfallRegular

/-! The same actual waterfall has coherent domains for every minimal roof development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- Construct the subdivision before its development, deriving all coherence needed at
reopening pinches. In particular no bank lift or compatible trace is a hypothesis. -/
theorem cornerExtendedOutward_exists_coherent_waterfall (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let covered := T.cornerTails_covers_rim inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ i : FiveSector,
      let E := insert (0 : ℂ) (Set.range (fun w :
        M.GeometricSectorLeaf F covered positive small lower i => w.point))
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        (∀ S ∈ P.cells, S.RecoverablePinchesIn E 0 cutoff) ∧
        ∀ D : FacewiseDevelopment L.partition.pairedComplex R.retain,
          ∀ S ∈ P.cells, ∀ z, (z ∈ S.strictCarrier ∨ z ∈ E) →
            z.re + z.im ∈ Set.Icc 0 cutoff →
              K.projectedVertex origin + (fiveSectorFrame t positive small i).place.symm z ∈
                Q.footprint ∧ D.ProjectedCoherentAt Q
                  (K.projectedVertex origin +
                    (fiveSectorFrame t positive small i).place.symm z) := by
  have controlled := M.cornerExtendedOutward_exists_regular_coherent_waterfall positive small T
    internal source_height lower conforming height cutoff deep
  refine fun i => ?_
  obtain ⟨P, pinches, _, physical⟩ := controlled i
  exact ⟨P, pinches, physical⟩

end Unfoldings.ConvexCap.SectorForest
