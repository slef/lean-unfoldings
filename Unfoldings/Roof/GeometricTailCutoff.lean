module

public import Unfoldings.Roof.GeometricSectorData
public import Unfoldings.Cap.GeometricTailCutoff

/-! A deep physical roof clip puts every actual tail endpoint beyond the chosen sweep slab. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

theorem geometricRootPath_end_tip (frame : Plane ≃ₗᵢ[ℝ] ℂ) (w : F.GeometricVertex) :
    (M.geometricRootPath F covered positive small frame w).vertex (Fin.last _) =
      frame ((F.componentTail (M.geometricComponent F covered w)).tip -
        origin) := by
  let P := M.geometricParents F covered positive small
  obtain ⟨c, root_eq⟩ := P.root_mem w
  have at_tip : (M.geometricParent F covered)^[P.distanceToRoot w] w = Sum.inr (Sum.inr c) :=
    (P.iterate_distanceToRoot_eq_root w).trans root_eq.symm
  have label := M.geometricComponent_iterate F covered w (P.distanceToRoot w)
  rw [at_tip] at label
  change c = M.geometricComponent F covered w at label
  change frame (F.geometricPosition ((M.geometricParent F covered)^[P.distanceToRoot w] w) -
    origin) = _
  rw [at_tip, ← label]
  rfl

namespace GeometricSectorLeaf

variable {M F covered positive small} {i : FiveSector}

/-- The cutoff is chosen from the actual clip before any leaf enumeration or strip insertion. -/
theorem tail_end_beyond_clip_ball
    (w : M.GeometricSectorLeaf F covered positive small i) {radius : ℝ}
    (inside : Metric.closedBall (origin) radius ⊆
      interior outer) :
    radius < M.geometricTailEndHeight F covered positive small i w.val := by
  let B := fiveSectorFrame t positive small i
  let c := M.geometricComponent F covered w.val
  let tip := (F.componentTail c).tip
  have outside : radius < dist (origin) tip :=
    by
      by_contra close
      apply (F.componentTail c).boundary.2
      apply inside
      rw [Metric.mem_closedBall, dist_comm]
      exact le_of_not_gt close
  have position := w.component_positions (Sum.inr (Sum.inr c)) rfl
  have coordinates := B.quadrant_nonneg position
  have norm_bound : dist (origin) tip ≤
      (B.place (tip - origin)).re +
        (B.place (tip - origin)).im := by
    calc
      _ = ‖tip - origin‖ := dist_eq_norm' _ _
      _ = ‖B.place (tip - origin)‖ := (B.place.norm_map _).symm
      _ ≤ _ := complex_norm_le_diagonal_of_nonneg coordinates.1 coordinates.2
  change radius <
    ((M.geometricRootPath F covered positive small B.place w.val).vertex (Fin.last _)).re +
      ((M.geometricRootPath F covered positive small B.place w.val).vertex (Fin.last _)).im
  rw [M.geometricRootPath_end_tip F covered positive small]
  exact outside.trans_le norm_bound

end GeometricSectorLeaf
end ConvexRoof.SectorForest
end Unfoldings
