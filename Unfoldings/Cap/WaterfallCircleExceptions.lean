module

public import Unfoldings.Cap.EmptyCircleStripBounds
public import Unfoldings.Cap.RegularCircleRadius

/-! One finite radius set covers all actual vertex values and every disappearing-strip exception. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (N : K.RadialCutForest source cuts)
  {t : ℝ} (positive : 0 < t) (small : t < 1) (D : FacewiseDevelopment C N.retain)
  (calibration : Plane ≃ₗᵢ[ℝ] ℂ) {ε cutoff : ℝ}
  (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
  (traces : ∀ i : FiveSector, ∀ cell : {S : MonotoneStrip // S ∈ (P i).cells},
    N.RadialStripTraceData positive small D calibration i cell.val ε cutoff)

def waterfallCircleExceptions : Set ℝ :=
  D.fiveSectorVertexRadii K source calibration positive small ∪
    ⋃ i : FiveSector, ⋃ cell : {S : MonotoneStrip // S ∈ (P i).cells},
      (traces i cell).emptyCircleExceptions

theorem finite_waterfallCircleExceptions :
    (N.waterfallCircleExceptions positive small D calibration P traces).Finite := by
  let : ∀ i : FiveSector, Finite {S : MonotoneStrip // S ∈ (P i).cells} :=
    fun i => (P i).cells.finite_toSet.to_subtype
  exact (D.finite_fiveSectorVertexRadii K source calibration positive small).union
    (Set.finite_iUnion (fun _ => Set.finite_iUnion (fun _ =>
      RadialStripTraceData.finite_emptyCircleExceptions _)))

theorem vertex_radius_not_mem_of_not_waterfallCircleExceptions {radius : ℝ}
    (outside : radius ∉ N.waterfallCircleExceptions positive small D calibration P traces) :
    radius ∉ D.fiveSectorVertexRadii K source calibration positive small :=
  fun member => outside (Or.inl member)

theorem empty_radius_not_mem_of_not_waterfallCircleExceptions {radius : ℝ}
    (outside : radius ∉ N.waterfallCircleExceptions positive small D calibration P traces)
    (i : FiveSector) (cell : {S : MonotoneStrip // S ∈ (P i).cells}) :
    radius ∉ (traces i cell).emptyCircleExceptions :=
  fun member => outside (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨cell, member⟩⟩))

end Unfoldings.ConvexCap.RadialCutForest
