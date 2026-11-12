module

public import Unfoldings.Cap.ClosedStripPathProgress
public import Unfoldings.Cap.CompletedBankChains
public import Unfoldings.Cap.SectorPositionMargins

/-! Actual completed parent paths give strict closed-trace progress through branch vertices. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {t : ℝ} {positive : 0 < t} {small : t < 1} {D : FacewiseDevelopment C N.retain}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}
  (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

/-- Actual closed bank points on one sector-controlled parent path progress in both
coordinates. Neither point needs to avoid fine vertices or exceptional circles. -/
theorem closed_coordinates_strict_on_completed_parent_path (nonnegative : 0 ≤ ε)
    (linear_error : ∀ f z,
      ‖(D.coordinatePlacement K calibration (fiveSectorFrame t positive small i).place f).linear z -
        z‖ ≤ ε * ‖z‖)
    (w : C.Vertex Set.univ)
    (directions : ∀ j, K.projectedVertex
      (N.spanningCompletion.parents.parent (N.completedBankChain w j).val) -
        K.projectedVertex (N.completedBankChain w j).val ∈ closedFiveSector t i)
    {μ : ℝ} (numerical : 2 * ε < μ)
    (margin : ∀ z ∈ (fiveSectorFrame t positive small i).enclosingStrip.carrier,
      0 ≤ z.re + z.im → μ * (z.re + z.im) ≤ z.re ∧ μ * (z.re + z.im) ≤ z.im)
    (j k : Fin (N.spanningCompletion.parents.distanceToRoot w)) (s r : unitInterval)
    {p q : ℂ} (first : p ∈ closure data.strictDomain) (last : q ∈ closure data.strictDomain)
    (first_physical : source + (fiveSectorFrame t positive small i).place.symm p =
      (N.completedRootPath w).point j s)
    (last_physical : source + (fiveSectorFrame t positive small i).place.symm q =
      (N.completedRootPath w).point k r)
    (ordered : p.re + p.im < q.re + q.im) :
    (data.value p).re < (data.value q).re ∧ (data.value p).im < (data.value q).im := by
  let frame := (fiveSectorFrame t positive small i).place
  let P : PolygonalChain ℂ (N.spanningCompletion.parents.distanceToRoot w) :=
    ⟨fun a => frame ((N.completedRootPath w).vertex a - source)⟩
  have edge (a : Fin (N.spanningCompletion.parents.distanceToRoot w)) :
      P.edge a = frame (K.projectedVertex
        (N.spanningCompletion.parents.parent (N.completedBankChain w a).val) -
          K.projectedVertex (N.completedBankChain w a).val) := by
    simp only [P, PolygonalChain.edge, completedRootPath, completedBankChain,
      Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply', map_sub]
    abel
  have edge_positive (a) : 0 < (P.edge a).re ∧ 0 < (P.edge a).im := by
    rw [edge]
    exact (fiveSectorFrame t positive small i).quadrant_self (directions a)
      (N.completed_parent_direction_ne_zero _ (N.completedBankChain w a).property)
  have edge_margins (a) :
      μ * ((P.edge a).re + (P.edge a).im) ≤ (P.edge a).re ∧
      μ * ((P.edge a).re + (P.edge a).im) ≤ (P.edge a).im :=
    margin (P.edge a)
      ((edge a).symm ▸ (fiveSectorFrame t positive small i).enclosingStrip_mem (directions a))
      (add_nonneg (edge_positive a).1.le (edge_positive a).2.le)
  have point (a) (u : unitInterval) :
      P.point a u = frame ((N.completedRootPath w).point a u - source) := by
    simp only [P, PolygonalChain.point, AffineMap.lineMap_apply_module', map_add, map_sub, map_smul]
    module
  have first_point : p = P.point j s := by
    rw [point, ← first_physical]
    simp only [add_sub_cancel_left, frame, LinearIsometryEquiv.apply_symm_apply]
  have last_point : q = P.point k r := by
    rw [point, ← last_physical]
    simp only [add_sub_cancel_left, frame, LinearIsometryEquiv.apply_symm_apply]
  rw [first_point] at first
  rw [last_point] at last
  rw [first_point, last_point] at ordered ⊢
  exact data.closed_coordinates_strict_on_margin_path nonnegative linear_error P numerical
    (fun a => add_nonneg (edge_positive a).1.le (edge_positive a).2.le) edge_margins
    j k s r first last ordered

end Unfoldings.ConvexCap.RadialCutForest.RadialStripTraceData
