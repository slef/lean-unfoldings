module

public import Unfoldings.Cap.ContactSeparatorValues
public import Unfoldings.Cap.RadialStripClosedBanks
public import Unfoldings.Cap.SharedBankCirclePrefix
public import Unfoldings.Cap.ExtendedWaterfallDomains

/-! Shared separator prefixes remain coherent through approached terminal pinches. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v u₁ v₁

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (leaf : M.GeometricSectorLeaf F covered positive small lower i)

/-- Actual approached prefix values agree even if either strip ends at this height.
Only active points below the tested height are used in the limiting argument. -/
theorem closed_shared_separator_prefix_value_of_contact
    {FineFace : Type u₁} [Fintype FineFace] {FineC : TriangleComplex.{u₁, v₁} FineFace}
    {Q : ConvexCap FineC}
    (R : Q.RadialCutForest (K.projectedVertex origin) (M.extendedGeometricCuts F))
    (D : FacewiseDevelopment FineC R.retain) (calibration : Plane ≃ₗᵢ[ℝ] ℂ)
    {cutoff ε : ℝ}
    (deep : Metric.closedBall (K.projectedVertex origin) cutoff ⊆ interior (K.clipFootprint Z))
    (P : (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (represented : ∀ w : M.GeometricSectorLeaf F covered positive small lower i,
      w.point.re + w.point.im ≤ cutoff → ∃ G ∈ P.separators,
        MonotoneStrip.CompletesTail w.point w.tailGraph.graph cutoff G)
    (traces : ∀ S ∈ P.cells, Nonempty
      (R.RadialStripTraceData positive small D calibration i S ε cutoff))
    {H : MonotoneHeightGraph} (separator : H ∈ P.separators)
    (active : leaf.point.re + leaf.point.im ≤ cutoff)
    (completion : MonotoneStrip.CompletesTail leaf.point leaf.tailGraph.graph cutoff H)
    (leaf_coherent : D.ProjectedCoherentAt Q (F.geometricPosition leaf.val))
    {S T : MonotoneStrip} (first_cell : S ∈ P.cells) (last_cell : T ∈ P.cells)
    (first_wall : S.upper = H) (last_wall : Set.EqOn H.point T.lower.point (Set.Icc 0 cutoff))
    (data : R.RadialStripTraceData positive small D calibration i S ε cutoff)
    (other : R.RadialStripTraceData positive small D calibration i T ε cutoff)
    {h : ℝ} (height : h ∈ Set.Icc 0 (leaf.point.re + leaf.point.im))
    (first_closed : S.upper.point h ∈ closure data.strictDomain)
    (last_closed : T.lower.point h ∈ closure other.strictDomain) :
    data.value (S.upper.point h) = other.value (T.lower.point h) := by
  by_cases zero : h = 0
  · obtain ⟨_, first_member⟩ := closure_nonempty_iff.mp ⟨_, first_closed⟩
    obtain ⟨_, last_member⟩ := closure_nonempty_iff.mp ⟨_, last_closed⟩
    rw [zero]
    exact (data.source_bank_values first_member).2.trans
      (other.source_bank_values last_member).1.symm
  have positive : 0 < h := lt_of_le_of_ne height.1 (Ne.symm zero)
  let good := {k : ℝ | data.value (S.upper.point k) = other.value (T.lower.point k)}
  have good_closed : IsClosed good :=
    isClosed_eq (data.continuous.comp S.upper.point_continuous)
      (other.continuous.comp T.lower.point_continuous)
  have inside : Set.Ioo 0 h ⊆ good := by
    intro k bounds
    obtain ⟨x, first_strict, first_slab, first_above⟩ :=
      MonotoneStrip.active_above_of_bank_mem_closure S.upper first_closed bounds.2
    obtain ⟨y, last_strict, last_slab, last_above⟩ :=
      MonotoneStrip.active_above_of_bank_mem_closure T.lower last_closed bounds.2
    have first_prior := data.upper_bank_closed_before first_closed
      (by rw [S.upper.point_height]; exact ⟨bounds.1.le, bounds.2.le⟩)
    have last_prior := other.lower_bank_closed_before last_closed
      (by rw [T.lower.point_height]; exact ⟨bounds.1.le, bounds.2.le⟩)
    exact leaf.shared_separator_prefix_value_of_contact R D calibration deep P represented traces
      separator
      active completion leaf_coherent first_cell last_cell first_wall last_wall data other
      ⟨bounds.1.le, bounds.2.le.trans height.2⟩
      ⟨first_above.le, first_slab.2⟩ (first_strict.1.trans first_strict.2)
      ⟨last_above.le, last_slab.2⟩ (last_strict.1.trans last_strict.2)
      first_prior last_prior
  have approached : h ∈ closure (Set.Ioo 0 h) := by
    rw [closure_Ioo positive.ne]
    exact ⟨positive.le, le_rfl⟩
  exact closure_minimal inside good_closed approached

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
