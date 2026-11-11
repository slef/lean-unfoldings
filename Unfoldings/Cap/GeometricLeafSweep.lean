module

public import Unfoldings.Cap.GeometricCutPaths
public import Unfoldings.Topology.DescendantLeavesWithin

/-! Each geometric component admits a height sweep in which every edge lies above a leaf. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

def geometricSweepHeight (frame : Plane ≃ₗᵢ[ℝ] ℂ) (w : F.GeometricVertex) : ℝ :=
  (frame (F.geometricPosition w - K.projectedVertex origin)).re +
    (frame (F.geometricPosition w - K.projectedVertex origin)).im

theorem geometricComponent_of_ancestor {w z : F.GeometricVertex}
    (reaches : (M.geometricParents F covered positive small lower).Ancestor w z) :
    M.geometricComponent F covered w = M.geometricComponent F covered z := by
  obtain ⟨n, at_z⟩ := reaches
  change (M.geometricParent F covered)^[n] w = z at at_z
  have label := M.geometricComponent_iterate F covered w n
  rw [at_z] at label
  exact label.symm

theorem geometricSweepHeight_parent_lt (i : FiveSector) (w : F.GeometricVertex)
    (nonroot : w ∉ (M.geometricParents F covered positive small lower).roots)
    (inside : F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
      closedFiveSector t i) :
    geometricSweepHeight F (fiveSectorFrame t positive small i).place w <
      geometricSweepHeight F (fiveSectorFrame t positive small i).place
        (M.geometricParent F covered w) := by
  let P := M.geometricParents F covered positive small lower
  let B := fiveSectorFrame t positive small i
  let direction := F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w
  have genuine : direction ≠ 0 := by
    intro zero
    have equal := F.geometricPosition_injective lower (sub_eq_zero.mp zero)
    have ascending := P.ascending w nonroot
    change P.height w < P.height (M.geometricParent F covered w) at ascending
    rw [equal] at ascending
    exact lt_irrefl _ ascending
  have frame_ne : B.place direction ≠ 0 := by
    simpa only [map_zero] using B.place.injective.ne genuine
  have close : InnerProductGeometry.angle (B.place direction) (B.place direction) < B.margin := by
    rw [InnerProductGeometry.angle_self frame_ne]
    exact B.positive
  have quadrant := B.quadrant_of_angle_close inside genuine close
  have difference : B.place (F.geometricPosition (M.geometricParent F covered w) -
      K.projectedVertex origin) - B.place (F.geometricPosition w - K.projectedVertex origin) =
        B.place direction := by
    rw [← map_sub]
    congr 1
    dsimp only [direction]
    abel
  have real := congrArg Complex.re difference
  have imaginary := congrArg Complex.im difference
  simp only [Complex.sub_re, Complex.sub_im] at real imaginary
  change (B.place _).re + (B.place _).im < (B.place _).re + (B.place _).im
  linarith [quadrant.1, quadrant.2]

/-- Minimize the sweep height among descendants. Every selected edge is above a genuine
childless leaf of the same component, independently of auxiliary mesh vertices. -/
theorem exists_geometric_component_leaf_sweep (c : F.Component) :
    ∃ i : FiveSector, ∀ w : F.GeometricVertex,
      w ∉ (M.geometricParents F covered positive small lower).roots →
      M.geometricComponent F covered w = c →
      ∃ leaf : F.GeometricVertex,
        (M.geometricParents F covered positive small lower).Ancestor leaf w ∧
        leaf ∉ (M.geometricParents F covered positive small lower).roots ∧
        geometricSweepHeight F (fiveSectorFrame t positive small i).place leaf ≤
          geometricSweepHeight F (fiveSectorFrame t positive small i).place w ∧
        (∀ child ∉ (M.geometricParents F covered positive small lower).roots,
          M.geometricParent F covered child ≠ leaf) ∧
        M.geometricComponent F covered leaf = c := by
  let P := M.geometricParents F covered positive small lower
  obtain ⟨i, directions⟩ := M.exists_geometric_component_sector F covered positive small lower c
  refine ⟨i, fun w nonroot component => ?_⟩
  obtain ⟨leaf, reaches, leaf_nonroot, height, childless⟩ :=
    P.exists_descendant_leaf_within
      (geometricSweepHeight F (fiveSectorFrame t positive small i).place) w nonroot
      (fun z ancestor z_nonroot => M.geometricSweepHeight_parent_lt F covered positive small lower
        i z z_nonroot (directions z z_nonroot
          ((M.geometricComponent_of_ancestor F covered positive small lower ancestor).trans
            component)))
  exact ⟨leaf, reaches, leaf_nonroot, height, childless,
    (M.geometricComponent_of_ancestor F covered positive small lower reaches).trans component⟩

end Unfoldings.ConvexCap.SectorForest
