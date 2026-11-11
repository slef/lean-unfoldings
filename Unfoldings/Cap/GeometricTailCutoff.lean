module

public import Unfoldings.Cap.GeometricSectorData
public import Unfoldings.Cap.DeepRoofClips

/-! A deep physical roof clip puts every actual tail endpoint beyond the chosen sweep slab. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem complex_norm_le_diagonal_of_nonneg {z : ℂ} (real : 0 ≤ z.re) (imaginary : 0 ≤ z.im) :
    ‖z‖ ≤ z.re + z.im := by
  simpa only [abs_of_nonneg real, abs_of_nonneg imaginary] using
    Complex.norm_le_abs_re_add_abs_im z

namespace ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

theorem geometricRootPath_end_tip (frame : Plane ≃ₗᵢ[ℝ] ℂ) (w : F.GeometricVertex) :
    (M.geometricRootPath F covered positive small lower frame w).vertex (Fin.last _) =
      frame ((F.componentTail (M.geometricComponent F covered w)).tip -
        K.projectedVertex origin) := by
  let P := M.geometricParents F covered positive small lower
  obtain ⟨c, root_eq⟩ := P.root_mem w
  have at_tip : (M.geometricParent F covered)^[P.distanceToRoot w] w = Sum.inr (Sum.inr c) :=
    (P.iterate_distanceToRoot_eq_root w).trans root_eq.symm
  have label := M.geometricComponent_iterate F covered w (P.distanceToRoot w)
  rw [at_tip] at label
  change c = M.geometricComponent F covered w at label
  change frame (F.geometricPosition ((M.geometricParent F covered)^[P.distanceToRoot w] w) -
    K.projectedVertex origin) = _
  rw [at_tip, ← label]
  rfl

namespace GeometricSectorLeaf

variable {M F covered positive small lower} {i : FiveSector}

/-- The cutoff is chosen from the actual clip before any leaf enumeration or strip insertion. -/
theorem tail_end_beyond_clip_ball
    (w : M.GeometricSectorLeaf F covered positive small lower i) {radius : ℝ}
    (inside : Metric.closedBall (K.projectedVertex origin) radius ⊆
      interior (K.clipFootprint Z)) :
    radius < M.geometricTailEndHeight F covered positive small lower i w.val := by
  let B := fiveSectorFrame t positive small i
  let c := M.geometricComponent F covered w.val
  let tip := (F.componentTail c).tip
  have outside : radius < dist (K.projectedVertex origin) tip :=
    K.clip_frontier_distance_gt inside (F.componentTail c).boundary
  have position := w.component_positions (Sum.inr (Sum.inr c)) rfl
  have coordinates := B.quadrant_nonneg position
  have norm_bound : dist (K.projectedVertex origin) tip ≤
      (B.place (tip - K.projectedVertex origin)).re +
        (B.place (tip - K.projectedVertex origin)).im := by
    calc
      _ = ‖tip - K.projectedVertex origin‖ := dist_eq_norm' _ _
      _ = ‖B.place (tip - K.projectedVertex origin)‖ := (B.place.norm_map _).symm
      _ ≤ _ := complex_norm_le_diagonal_of_nonneg coordinates.1 coordinates.2
  change radius <
    ((M.geometricRootPath F covered positive small lower B.place w.val).vertex (Fin.last _)).re +
      ((M.geometricRootPath F covered positive small lower B.place w.val).vertex (Fin.last _)).im
  rw [M.geometricRootPath_end_tip F covered positive small lower]
  exact outside.trans_le norm_bound

end GeometricSectorLeaf
end ConvexCap.SectorForest
end Unfoldings
