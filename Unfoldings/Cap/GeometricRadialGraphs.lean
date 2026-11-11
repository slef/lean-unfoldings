module

public import Unfoldings.Cap.GeometricRadialEdges
public import Unfoldings.Geometry.RayHeightSegments

/-! Construct the exact source-ray graph of the radial edge of every active cut component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} {M : K.SectorForest t origin}
  {Z : ℝ} {F : K.SkirtTailFamily Z (K.projectedVertex origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {lower : Z < 0} {i : FiveSector}
  (w : M.GeometricSectorLeaf F covered positive small lower i)

theorem exists_radial_heightGraph :
    let B := fiveSectorFrame t positive small i
    let c := M.geometricComponent F covered w.val
    let seed := B.place (F.componentSeed c - K.projectedVertex origin)
    let tip := B.place ((F.componentTail c).tip - K.projectedVertex origin)
    ∃ G : MonotoneHeightGraph,
      (∀ h, G.coordinate h = G.coordinate 1 * h) ∧
      (∀ x ∈ (F.componentTail c).carrier,
        G.point ((B.place (x - K.projectedVertex origin)).re +
          (B.place (x - K.projectedVertex origin)).im) =
            B.place (x - K.projectedVertex origin)) ∧
      ∀ h ∈ Set.Icc (seed.re + seed.im) (tip.re + tip.im),
        G.point h ∈ (M.sectorHeightNetwork F covered positive small lower i).carrier := by
  let B := fiveSectorFrame t positive small i
  let c := M.geometricComponent F covered w.val
  let T := F.componentTail c
  let seed := B.place (F.componentSeed c - K.projectedVertex origin)
  let tip := B.place (T.tip - K.projectedVertex origin)
  have tip_ne : T.tip - K.projectedVertex origin ≠ 0 := by
    intro zero
    have inside := K.original_footprint_in_clip_interior lower (interior_subset F.origin)
    exact T.boundary.2 ((sub_eq_zero.mp zero).symm ▸ inside)
  have tip_inside : T.tip - K.projectedVertex origin ∈ closedFiveSector t i :=
    w.component_positions (Sum.inr (Sum.inr c)) rfl
  have quadrant := B.quadrant_self tip_inside tip_ne
  let G := MonotoneHeightGraph.ray tip quadrant.1 quadrant.2
  have seed_ray : seed = T.start • tip := by
    have vector : F.componentSeed c - K.projectedVertex origin =
        T.start • (T.tip - K.projectedVertex origin) := by
      have vector := congrArg (fun p : Plane => p - K.projectedVertex origin) T.seed_eq
      change F.componentSeed c - K.projectedVertex origin =
        (K.projectedVertex origin + T.start • (T.tip - K.projectedVertex origin)) -
          K.projectedVertex origin at vector
      simpa only [add_sub_cancel_left] using vector
    exact (congrArg B.place vector).trans (B.place.map_smul _ _)
  refine ⟨G, ?_, ?_, ?_⟩
  · intro h
    simp only [G, MonotoneHeightGraph.ray_coordinate, mul_one]
  · intro x member
    obtain ⟨r, _, expression⟩ := T.carrier_eq_image.subset member
    have position : B.place (x - K.projectedVertex origin) = r • tip := by
      rw [← expression, add_sub_cancel_left, map_smul]
    rw [position]
    exact MonotoneHeightGraph.ray_point_smul_tip _ _ _ r
  · intro h slab
    obtain ⟨z, nonroot, component, first, parent⟩ :=
      M.exists_geometric_component_radial_edge F covered positive small lower c
        (M.geometric_component_nonconstant F covered positive small lower w.val w.property.1)
    let e : M.GeometricSectorEdge F covered positive small lower i :=
      ⟨z, nonroot, w.component_directions z nonroot component⟩
    let N := M.sectorHeightNetwork F covered positive small lower i
    have first_eq : N.first e = seed := by
      change centeredPlaneFrame _ _ _ = _
      rw [centeredPlaneFrame_apply]
      change B.place (F.geometricPosition z - K.projectedVertex origin) = seed
      rw [first]
    have last_eq : N.last e = tip := by
      change centeredPlaneFrame _ _ _ = _
      rw [centeredPlaneFrame_apply]
      change B.place (F.geometricPosition (M.geometricParent F covered z) -
        K.projectedVertex origin) = tip
      rw [parent]
      rfl
    have first_on_ray : G.point (seed.re + seed.im) = seed := by
      rw [seed_ray]
      exact MonotoneHeightGraph.ray_point_smul_tip _ _ _ _
    have cover := N.radial_edge_graph_covered e
      (last_eq.symm ▸ quadrant.1) (last_eq.symm ▸ quadrant.2)
      (by
        rw [MonotoneHeightGraph.ray_point_eq_smul, first_eq, last_eq]
        rw [MonotoneHeightGraph.ray_point_eq_smul] at first_on_ray
        exact first_on_ray)
      (by rw [first_eq, last_eq]; exact slab)
    simpa only [G, MonotoneHeightGraph.ray_point_eq_smul, last_eq] using cover

end Unfoldings.ConvexCap.SectorForest.GeometricSectorLeaf
