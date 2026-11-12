module

public import Unfoldings.Cap.ExtendedRegularBankTraces
public import Unfoldings.Cap.ExtendedWaterfallCoherent

/-! Complete actual bank traces start at the common source and retain one-sided face visibility. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- Both actual bank curves up to every active height belong to the constructed one-sided
trace, including the source and isolated leaf pinches. Each value is approached through its
own containing face. Neither boundary parametrizations nor compatible lifts are assumed. -/
theorem cornerExtendedOutward_exists_waterfall_bank_traces (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) (cutoff : ℝ)
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z)) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
    ∀ i : FiveSector,
      ∃ P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision,
        ∀ (D : FacewiseDevelopment L.partition.pairedComplex R.retain)
          (calibration : Plane ≃ₗᵢ[ℝ] ℂ), ∀ S ∈ P.cells,
          let frame := (fiveSectorFrame t positive small i).place
          let domain := {z | z ∈ S.strictCarrier ∧ z.re + z.im ∈ Set.Icc 0 cutoff}
          LipschitzOnWith 8 (D.centeredMap Q (K.projectedVertex origin) calibration frame) domain ∧
          ∃ G : ℂ → ℂ, Continuous G ∧
            Set.EqOn (D.centeredMap Q (K.projectedVertex origin) calibration frame) G domain ∧
            ∀ z ∈ domain,
              G 0 = D.centeredMap Q (K.projectedVertex origin) calibration frame 0 ∧
              ∀ h ∈ Set.Icc 0 (z.re + z.im),
                D.TraceVisibleAt Q (K.projectedVertex origin) calibration frame G domain
                  (S.lower.point h) ∧
                D.TraceVisibleAt Q (K.projectedVertex origin) calibration frame G domain
                  (S.upper.point h) := by
  have controlled := M.cornerExtendedOutward_exists_regular_waterfall_bank_traces positive small T
    internal source_height lower conforming height cutoff deep
  refine fun i => ?_
  obtain ⟨P, _, _, traces⟩ := controlled i
  exact ⟨P, traces⟩

end Unfoldings.ConvexCap.SectorForest
