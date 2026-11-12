module

public import Unfoldings.Cap.ExtendedRegularBankTraces
public import Unfoldings.Cap.RegularWaterfallBankWidth
public import Unfoldings.Cap.MatchedBankTrace

/-! Construct actual waterfall traces with named regular bank matching, deriving all geometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin) {Z : ℝ}

/-- The waterfall precedes its development and calibration. Width, cut avoidance, and
all one-sided bank values are constructed; regular pieces match the actual named banks. -/
theorem cornerExtendedOutward_exists_matched_bank_traces (positive : 0 < t) (small : t < 1)
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
          ∃ G : ℂ → ℂ, Continuous G ∧
            Set.EqOn (D.centeredMap Q (K.projectedVertex origin) calibration frame) G domain ∧
            R.MatchesParentBanks positive small i (R.completedDevelopment D)
              calibration G S cutoff := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have controlled := M.cornerExtendedOutward_exists_regular_waterfall_bank_traces positive small T
    internal source_height lower conforming height cutoff deep
  refine fun i => ?_
  obtain ⟨P, pinches, geometric, traces⟩ := controlled i
  refine ⟨P, fun D calibration S cell => ?_⟩
  obtain ⟨_, G, continuous, equal, trace⟩ := traces D calibration S cell
  refine ⟨G, continuous, equal, ?_⟩
  apply R.matchesParentBanks_of_visible_traces positive small i (R.completedDevelopment D)
    calibration G S cutoff
  · intro z strict slab
    exact (geometric S cell z strict slab).2
  · intro z member slab regular k active width
    exact M.regular_waterfall_bank_width F covered positive small lower T i P S cell cutoff deep
      (pinches S cell) member slab regular active width
  · intro active strict slab h within
    exact (trace active ⟨strict, slab⟩).2 h within

end Unfoldings.ConvexCap.SectorForest
