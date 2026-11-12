module

public import Unfoldings.Cap.BoundaryRunClosedPrefix
public import Unfoldings.Cap.CoherentEmptyCircleExclusion

/-! A neighboring circle crossing before a boundary-run terminal cannot be coherent. -/

@[expose] public section

namespace Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  (B : N.FiveSectorFrameData positive small (N.completedDevelopment D))
  (i : FiveSector) {ε cutoff physicalRadius radius : ℝ} {n : ℕ}
  (cells : Fin (n + 1) → MonotoneStrip)
  (traces : ∀ j, N.RadialStripTraceData positive small D
    (N.calibratedFrame (N.completedDevelopment D) B.anchor B.reference) i (cells j) ε cutoff)
  (contacts : ∀ j : Fin n, Set.EqOn (cells j.castSucc).upper.point
    (cells j.succ).lower.point (Set.Icc 0 cutoff))
  (terminals : ∀ j, B.EmptyCircleContinuation i (traces j) physicalRadius radius)
  (pivot : Fin (n + 1))
  (radius_positive : 0 < radius)
  (outside : ∀ k, radius ∉ (traces k).emptyCircleExceptions)
  (empty : ∀ k, (traces k).value '' (cells k).openSlab 0 cutoff ∩
    {w | ‖w - (traces k).center‖ = radius} = ∅)
  {otherCalibration : Plane ≃ₗᵢ[ℝ] ℂ} {j : FiveSector} {T : MonotoneStrip} {δ limit : ℝ}
  (other : N.RadialStripTraceData positive small D otherCalibration j T δ limit)
  {z : ℂ} (closed : z ∈ closure other.strictDomain)
  (size : ‖other.value z - other.center‖ = radius)

include contacts radius_positive outside empty closed size

theorem first_run_circle_after_terminal_or_not_coherent {h : ℝ} (positive_height : 0 < h)
    (outer : Set.EqOn (fiveSectorFrame t positive small i).enclosingStrip.lower.point
      (cells 0).lower.point (Set.Icc 0 cutoff))
    (contact : (fiveSectorFrame t positive small i).place.symm
        ((fiveSectorFrame t positive small i).enclosingStrip.lower.point h) =
      (fiveSectorFrame t positive small j).place.symm z) :
    (terminals pivot).height < h ∨
      ¬ D.ProjectedCoherentAt K
        (source + (fiveSectorFrame t positive small i).place.symm
          ((fiveSectorFrame t positive small i).enclosingStrip.lower.point h)) := by
  by_cases after : (terminals pivot).height < h
  · exact Or.inl after
  right
  intro coherent
  obtain ⟨k, at_boundary, approached⟩ := B.first_run_approached_boundary_prefix i cells traces
    contacts terminals pivot positive_height (not_lt.mp after) outer
  have physical : (fiveSectorFrame t positive small i).place.symm ((cells k).lower.point h) =
      (fiveSectorFrame t positive small j).place.symm z := by
    rw [← at_boundary]
    exact contact
  apply (traces k).not_coherent_of_empty_circle_contact other approached closed physical
    radius_positive (outside k) (empty k) size
  rwa [← at_boundary]

theorem last_run_circle_after_terminal_or_not_coherent {h : ℝ} (positive_height : 0 < h)
    (outer : Set.EqOn (cells (Fin.last n)).upper.point
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point (Set.Icc 0 cutoff))
    (contact : (fiveSectorFrame t positive small i).place.symm
        ((fiveSectorFrame t positive small i).enclosingStrip.upper.point h) =
      (fiveSectorFrame t positive small j).place.symm z) :
    (terminals pivot).height < h ∨
      ¬ D.ProjectedCoherentAt K
        (source + (fiveSectorFrame t positive small i).place.symm
          ((fiveSectorFrame t positive small i).enclosingStrip.upper.point h)) := by
  by_cases after : (terminals pivot).height < h
  · exact Or.inl after
  right
  intro coherent
  obtain ⟨k, at_boundary, approached⟩ := B.last_run_approached_boundary_prefix i cells traces
    contacts terminals pivot positive_height (not_lt.mp after) outer
  have physical : (fiveSectorFrame t positive small i).place.symm ((cells k).upper.point h) =
      (fiveSectorFrame t positive small j).place.symm z := by
    rw [← at_boundary]
    exact contact
  apply (traces k).not_coherent_of_empty_circle_contact other approached closed physical
    radius_positive (outside k) (empty k) size
  rwa [← at_boundary]

end Unfoldings.ConvexCap.RadialCutForest.FiveSectorFrameData
