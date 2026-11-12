module

public import Unfoldings.Cap.ExtendedWaterfallCoherent
public import Unfoldings.Cap.CenteredBankTrace
public import Unfoldings.Cap.DevelopedDirectionNorm

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
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let covered := T.cornerTails_covers_rim inside source_height lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := (M.cornerExtendedOutwardForest positive small T internal source_height lower).val
  have domain_control := M.cornerExtendedOutward_exists_coherent_waterfall positive small T
    internal source_height lower conforming height cutoff deep
  refine fun i => ?_
  obtain ⟨P, pinches, physical⟩ := domain_control i
  refine ⟨P, ?_⟩
  intro D calibration S cell
  let frame := (fiveSectorFrame t positive small i).place
  let E := insert (0 : ℂ) (Set.range (fun w :
    M.GeometricSectorLeaf F covered positive small lower i => w.point))
  have linear_bound (f) (z : ℂ) :
      ‖(D.coordinatePlacement Q calibration frame f).linear z‖ ≤ (2 : ℝ) * ‖z‖ := by
    have estimate := (D.coordinatePlacement_norm_bounds Q calibration frame f z).2
    have normal : (3 : ℝ) / 4 ≤ Q.normal f 2 := height (L.partition.face f)
    have product := mul_le_mul_of_nonneg_right normal
      (norm_nonneg ((D.coordinatePlacement Q calibration frame f).linear z))
    nlinarith [norm_nonneg z]
  have finite : E.Finite := (Set.finite_range (fun w :
    M.GeometricSectorLeaf F covered positive small lower i => w.point)).insert 0
  have root_source := (fiveSectorFrame t positive small i).enclosingStrip_source
  have source_bounds := P.cell_bounds cell 0
  rw [root_source.1, root_source.2] at source_bounds
  have ordered := S.ordered 0
  have first_source : S.lower.coordinate 0 = 0 :=
    le_antisymm (ordered.trans source_bounds.2) source_bounds.1
  have last_source : S.upper.coordinate 0 = 0 :=
    le_antisymm source_bounds.2 (source_bounds.1.trans ordered)
  constructor
  · simpa only [show (4 : ℝ≥0) * 2 = 8 by norm_num] using
      D.centeredMap_lipschitzOn_strip (K.projectedVertex origin) calibration frame 2
        linear_bound S E 0 cutoff (pinches S cell) (physical D S cell)
  · exact D.centeredMap_exists_bank_trace (K.projectedVertex origin) calibration frame 2
      linear_bound S E cutoff finite (Or.inl rfl) first_source last_source (pinches S cell)
      (physical D S cell)

end Unfoldings.ConvexCap.SectorForest
