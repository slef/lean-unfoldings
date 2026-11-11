module

public import Unfoldings.Cap.GeometricLeafSweep

/-! Every geometric cut-edge point lies above a descendant leaf in its component sweep. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem linear_segment_lower_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    (height : E →ₗ[ℝ] ℝ) {a b x : E} (ordered : height a ≤ height b)
    (member : x ∈ segment ℝ a b) : height a ≤ height x := by
  have inside : height x ∈ segment ℝ (height a) (height b) :=
    (image_segment ℝ height.toAffineMap a b).subset ⟨x, member, rfl⟩
  rw [segment_eq_Icc ordered] at inside
  exact inside.1

namespace ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

/-- This is the support fact for processing leaves in increasing height: every cut segment
below the next unprocessed leaf already belongs to an earlier leaf's parent path. -/
theorem exists_geometric_component_leaf_support (c : F.Component) :
    ∃ i : FiveSector, ∀ w : F.GeometricVertex,
      w ∉ (M.geometricParents F covered positive small lower).roots →
      M.geometricComponent F covered w = c → ∀ x ∈ segment ℝ (F.geometricPosition w)
        (F.geometricPosition (M.geometricParent F covered w)),
      ∃ leaf : F.GeometricVertex,
        (M.geometricParents F covered positive small lower).Ancestor leaf w ∧
        leaf ∉ (M.geometricParents F covered positive small lower).roots ∧
        geometricSweepHeight F (fiveSectorFrame t positive small i).place leaf ≤
          ((fiveSectorFrame t positive small i).place (x - K.projectedVertex origin)).re +
            ((fiveSectorFrame t positive small i).place (x - K.projectedVertex origin)).im ∧
        (∀ child ∉ (M.geometricParents F covered positive small lower).roots,
          M.geometricParent F covered child ≠ leaf) ∧
        M.geometricComponent F covered leaf = c := by
  let P := M.geometricParents F covered positive small lower
  obtain ⟨i, directions⟩ := M.exists_geometric_component_sector F covered positive small lower c
  let B := fiveSectorFrame t positive small i
  let height : Plane →ₗ[ℝ] ℝ :=
    (Complex.reCLM.toLinearMap + Complex.imCLM.toLinearMap).comp B.place.toLinearEquiv.toLinearMap
  refine ⟨i, fun w nonroot component x member => ?_⟩
  obtain ⟨leaf, reaches, leaf_nonroot, leaf_height, childless⟩ :=
    P.exists_descendant_leaf_within (geometricSweepHeight F B.place) w nonroot
      (fun z ancestor z_nonroot => M.geometricSweepHeight_parent_lt F covered positive small lower
        i z z_nonroot (directions z z_nonroot
          ((M.geometricComponent_of_ancestor F covered positive small lower ancestor).trans
            component)))
  have step := M.geometricSweepHeight_parent_lt F covered positive small lower i w nonroot
    (directions w nonroot component)
  change height (F.geometricPosition w - K.projectedVertex origin) <
    height (F.geometricPosition (M.geometricParent F covered w) - K.projectedVertex origin) at step
  simp only [map_sub] at step
  have ascending : height (F.geometricPosition w) ≤
      height (F.geometricPosition (M.geometricParent F covered w)) := by linarith
  have point_after : geometricSweepHeight F B.place w ≤
      (B.place (x - K.projectedVertex origin)).re +
        (B.place (x - K.projectedVertex origin)).im := by
    change height (F.geometricPosition w - K.projectedVertex origin) ≤
      height (x - K.projectedVertex origin)
    simp only [map_sub]
    exact sub_le_sub_right (linear_segment_lower_bound height ascending member) _
  exact ⟨leaf, reaches, leaf_nonroot, leaf_height.trans point_after, childless,
    (M.geometricComponent_of_ancestor F covered positive small lower reaches).trans component⟩

end ConvexCap.SectorForest
end Unfoldings
