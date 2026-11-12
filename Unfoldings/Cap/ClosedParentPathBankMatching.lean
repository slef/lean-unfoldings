module

public import Unfoldings.Cap.PositiveWidthBankStartOrder
public import Unfoldings.Cap.ApproachedVertexPinchWidth
public import Unfoldings.Cap.FramedVertexHeights
public import Unfoldings.Geometry.RecoverableStripClosure

/-! Compact actual bank graphs preserve whole-path matching through every vertex height. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) (w : C.Vertex Set.univ) (on_cuts : K.projectedVertex w ∈ cuts)
  (directions : ∀ j, K.projectedVertex
    (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
      K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
  {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i S ε cutoff)
  (pinches : S.ApproachedPinchesIn
    (Set.range (fun v : {v : C.Vertex Set.univ // K.projectedVertex v ∈ cuts} =>
      (fiveSectorFrame t positive small i).place (K.projectedVertex v.val - source))) 0 cutoff)
  {a b : ℝ} (start : 0 ≤ a) (ordered : a < b) (finish : b ≤ cutoff)

include on_cuts directions pinches start ordered finish

/-- Both physical parameters and the actual named developed bank survive at closed heights. -/
theorem lower_matches_completed_path_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.lower.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
          (N.completedRootPath w).point j s) :
    ∀ h ∈ Set.Icc a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) =
          (N.completedRootPath w).point j s ∧
        data.value (S.lower.point h) = B.sectorFrame i
          (N.parentEntrancePoint (N.completedDevelopment D) (N.completedBankChain w j)
            (1 - (s : ℝ))) := by
  let graph := fun j (s : unitInterval) =>
    ((N.completedRootPath w).point j s, B.sectorFrame i
      (N.parentEntrancePoint (N.completedDevelopment D) (N.completedBankChain w j)
        (1 - (s : ℝ))))
  let graphs := ⋃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), Set.range (graph j)
  have graphs_closed : IsClosed graphs := isClosed_iUnion_of_finite fun j => by
    apply IsCompact.isClosed
    apply isCompact_range
    apply Continuous.prodMk
    · exact AffineMap.lineMap_continuous.comp continuous_subtype_val
    · apply (B.sectorFrame i).continuous.comp
      dsimp only [parentEntrancePoint]
      fun_prop
  let actual := fun h : ℝ =>
    (source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h),
      data.value (S.lower.point h))
  have actual_continuous : Continuous actual :=
    (continuous_const.add ((fiveSectorFrame t positive small i).place.symm.continuous.comp
      S.lower.point_continuous)).prodMk (data.continuous.comp S.lower.point_continuous)
  have good : Set.Ioo a b \ K.framedVertexHeights source
      (fiveSectorFrame t positive small i).place ⊆ actual ⁻¹' graphs := by
    intro h member
    have regular := K.regular_of_not_framedVertexHeights source
      (fiveSectorFrame t positive small i).place
      (z := S.lower.point h) (by simpa only [S.lower.point_height] using member.2)
    have height : h ∈ Set.Ioo 0 cutoff :=
      ⟨start.trans_lt member.1.1, member.1.2.trans_le finish⟩
    have width := data.width_pos_of_approached_regular pinches
      height (closed h member.1) regular
    obtain ⟨j, s, physical⟩ := tracked h member.1
    have on_edge : source + (fiveSectorFrame t positive small i).place.symm (S.lower.point h) ∈
        segment ℝ (K.projectedVertex (N.completedBankChain w j).val)
          (K.projectedVertex (N.spanningCompletion.parents.parent
            (N.completedBankChain w j).val)) := by
      rw [physical, N.completedRootPath_point_bankChain]
      exact lineMap_mem_segment ℝ _ _ s.property
    have matching := (data.bank_matching.at_positive_width height width (N.completedBankChain w j)
      (N.completedRootPath_vertex_mem on_cuts j.castSucc) (directions j)).1 regular on_edge
    have value := matching.trans
      (B.centered_entrance_chart_eq_comparison_point i w 0 j s _ physical)
    rw [B.entranceComparisonChain_original_point] at value
    exact Set.mem_iUnion.mpr ⟨j, ⟨s, Prod.ext physical.symm value.symm⟩⟩
  intro h member
  have approached := Icc_subset_closure_Ioo_sdiff_finite ordered
    (K.finite_framedVertexHeights source (fiveSectorFrame t positive small i).place) member
  obtain ⟨j, s, equal⟩ := Set.mem_iUnion.mp
    (closure_minimal good (graphs_closed.preimage actual_continuous) approached)
  exact ⟨j, s, (congrArg Prod.fst equal).symm, (congrArg Prod.snd equal).symm⟩

/-- Both physical parameters and the actual named developed bank survive at closed heights. -/
theorem upper_matches_completed_path_on_closed_interval
    (closed : ∀ h ∈ Set.Ioo a b, S.upper.point h ∈ closure data.strictDomain)
    (tracked : ∀ h ∈ Set.Ioo a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
          (N.completedRootPath w).point j s) :
    ∀ h ∈ Set.Icc a b,
      ∃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), ∃ s : unitInterval,
        source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) =
          (N.completedRootPath w).point j s ∧
        data.value (S.upper.point h) = B.sectorFrame i
          (N.parentExitPoint (N.completedDevelopment D) (N.completedBankChain w j)
            (1 - (s : ℝ))) := by
  let graph := fun j (s : unitInterval) =>
    ((N.completedRootPath w).point j s, B.sectorFrame i
      (N.parentExitPoint (N.completedDevelopment D) (N.completedBankChain w j)
        (1 - (s : ℝ))))
  let graphs := ⋃ j : Fin (N.spanningCompletion.parents.distanceToRoot w), Set.range (graph j)
  have graphs_closed : IsClosed graphs := isClosed_iUnion_of_finite fun j => by
    apply IsCompact.isClosed
    apply isCompact_range
    apply Continuous.prodMk
    · exact AffineMap.lineMap_continuous.comp continuous_subtype_val
    · apply (B.sectorFrame i).continuous.comp
      dsimp only [parentExitPoint]
      fun_prop
  let actual := fun h : ℝ =>
    (source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h),
      data.value (S.upper.point h))
  have actual_continuous : Continuous actual :=
    (continuous_const.add ((fiveSectorFrame t positive small i).place.symm.continuous.comp
      S.upper.point_continuous)).prodMk (data.continuous.comp S.upper.point_continuous)
  have good : Set.Ioo a b \ K.framedVertexHeights source
      (fiveSectorFrame t positive small i).place ⊆ actual ⁻¹' graphs := by
    intro h member
    have regular := K.regular_of_not_framedVertexHeights source
      (fiveSectorFrame t positive small i).place
      (z := S.upper.point h) (by simpa only [S.upper.point_height] using member.2)
    have height : h ∈ Set.Ioo 0 cutoff :=
      ⟨start.trans_lt member.1.1, member.1.2.trans_le finish⟩
    have width := data.width_pos_of_upper_approached_regular pinches
      height (closed h member.1) regular
    obtain ⟨j, s, physical⟩ := tracked h member.1
    have on_edge : source + (fiveSectorFrame t positive small i).place.symm (S.upper.point h) ∈
        segment ℝ (K.projectedVertex (N.completedBankChain w j).val)
          (K.projectedVertex (N.spanningCompletion.parents.parent
            (N.completedBankChain w j).val)) := by
      rw [physical, N.completedRootPath_point_bankChain]
      exact lineMap_mem_segment ℝ _ _ s.property
    have matching := (data.bank_matching.at_positive_width height width (N.completedBankChain w j)
      (N.completedRootPath_vertex_mem on_cuts j.castSucc) (directions j)).2 regular on_edge
    have value := matching.trans
      (B.centered_exit_chart_eq_comparison_point i w 0 j s _ physical)
    rw [B.exitComparisonChain_original_point] at value
    exact Set.mem_iUnion.mpr ⟨j, ⟨s, Prod.ext physical.symm value.symm⟩⟩
  intro h member
  have approached := Icc_subset_closure_Ioo_sdiff_finite ordered
    (K.finite_framedVertexHeights source (fiveSectorFrame t positive small i).place) member
  obtain ⟨j, s, equal⟩ := Set.mem_iUnion.mp
    (closure_minimal good (graphs_closed.preimage actual_continuous) approached)
  exact ⟨j, s, (congrArg Prod.fst equal).symm, (congrArg Prod.snd equal).symm⟩

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
