module

public import Unfoldings.Cap.GeometricSectorBankPoints
public import Unfoldings.Roof.GeometricTailBankContacts
public import Unfoldings.Roof.GeometricRadialGraphs
public import Unfoldings.Roof.GeometricTailCutoff

/-! An actual tail cannot leave an exterior sector bank after contacting it beyond its leaf. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} {M : K.SectorForest t origin}
  {outer : Set Plane} {F : K.SkirtTailFamily outer (origin)}
  {covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier}
  {positive : 0 < t} {small : t < 1} {i : FiveSector}
  (w : M.GeometricSectorLeaf F covered positive small i)

theorem tailGraph_enclosing_wall_sticks (H : MonotoneHeightGraph)
    (wall : H = (fiveSectorFrame t positive small i).enclosingStrip.lower ∨
      H = (fiveSectorFrame t positive small i).enclosingStrip.upper)
    {h b : ℝ} (after : w.point.re + w.point.im < h) (within : h ≤ b)
    (finish : b < M.geometricTailEndHeight F covered positive small i w.val)
    (same : H.coordinate h = w.tailGraph.graph.coordinate h) :
    ∀ k ∈ Set.Icc h b, H.coordinate k = w.tailGraph.graph.coordinate k := by
  let B := fiveSectorFrame t positive small i
  let c := M.geometricComponent F covered w.val
  let T := F.componentTail c
  let seed := B.place (F.componentSeed c - origin)
  let tip := B.place (T.tip - origin)
  let A := centeredPlaneFrame (origin) B.place
  let x := origin + B.place.symm (w.tailGraph.graph.point h)
  have point_at : B.place (x - origin) = w.tailGraph.graph.point h := by
    simp only [x, add_sub_cancel_left, B.place.apply_symm_apply]
  have wall_point : H.point h = w.tailGraph.graph.point h := by
    apply Complex.ext
    · exact same
    · change h - H.coordinate h = h - w.tailGraph.graph.coordinate h
      rw [same]
  have bank : x - origin ∉ strictFiveSector t i := by
    have banks := fiveSector_enclosingStrip_bank_not_strict positive small i h
    have inverse : x - origin = B.place.symm (H.point h) := by
      rw [wall_point]
      exact (B.place.symm_apply_apply _).symm.trans (congrArg B.place.symm point_at)
    rw [inverse]
    rcases wall with equal | equal
    · exact equal.symm ▸ banks.1
    · exact equal.symm ▸ banks.2
  have radial := w.tail_bank_contact_radial point_at after (within.trans_lt finish) bank
  obtain ⟨R, homogeneous, agreement, cover⟩ := w.exists_radial_heightGraph
  have x_height : (B.place (x - origin)).re +
      (B.place (x - origin)).im = h := by
    rw [point_at, w.tailGraph.graph.point_height]
  have at_radial : R.point h = w.tailGraph.graph.point h := by
    have equal := agreement x radial
    change R.point ((B.place (x - origin)).re +
      (B.place (x - origin)).im) = B.place (x - origin)
      at equal
    rwa [x_height, point_at] at equal
  have tip_height : tip.re + tip.im =
      M.geometricTailEndHeight F covered positive small i w.val := by
    change _ = ((M.geometricRootPath F covered positive small B.place w.val).vertex
      (Fin.last _)).re +
        ((M.geometricRootPath F covered positive small B.place w.val).vertex (Fin.last _)).im
    rw [M.geometricRootPath_end_tip F covered positive small]
  have seed_before : seed.re + seed.im ≤ h := by
    have image : A '' segment ℝ (F.componentSeed c) T.tip = segment ℝ seed tip :=
      by
        have raw : A '' segment ℝ (F.componentSeed c) T.tip =
            segment ℝ (A (F.componentSeed c)) (A T.tip) :=
          image_segment ℝ A.toAffineMap _ _
        rw [show A (F.componentSeed c) = seed from centeredPlaneFrame_apply _ _ _,
          show A T.tip = tip from centeredPlaneFrame_apply _ _ _] at raw
        exact raw
    have on_segment : B.place (x - origin) ∈ segment ℝ seed tip := by
      have member := image.subset ⟨x, radial, rfl⟩
      simpa only [A, centeredPlaneFrame_apply] using member
    have heights : h ∈ segment ℝ (seed.re + seed.im) (tip.re + tip.im) := by
      have image := image_segment ℝ complexDiagonalHeight.toAffineMap seed tip
      have member := image.subset ⟨_, on_segment, rfl⟩
      change (B.place (x - origin)).re +
        (B.place (x - origin)).im ∈
          segment ℝ (seed.re + seed.im) (tip.re + tip.im) at member
      rwa [x_height] at member
    rw [segment_eq_uIcc] at heights
    exact (min_le_iff.mp heights.1).resolve_right
      (within.trans_lt (finish.trans_eq tip_height.symm)).not_ge
  let N := M.sectorHeightNetwork F covered positive small i
  have joined : w.tailGraph.graph.CoalescesOn R h b := N.graphs_coalesce _ _
    (fun k slab => w.tailGraph.covered k (after.le.trans slab.1) (slab.2.trans_lt finish))
    (fun k slab => cover k ⟨seed_before.trans slab.1,
      (slab.2.trans_lt finish).le.trans_eq tip_height.symm⟩)
  have hpositive : 0 < h := (add_nonneg w.point_nonnegative.1 w.point_nonnegative.2).trans_lt after
  have wall_homogeneous {k : ℝ} (nonnegative : 0 ≤ k) :
      H.coordinate k = H.coordinate 1 * k := by
    rcases wall with equal | equal
    · rw [equal]
      exact (B.enclosingStrip_coordinate_homogeneous nonnegative).1
    · rw [equal]
      exact (B.enclosingStrip_coordinate_homogeneous nonnegative).2
  have coefficients : H.coordinate 1 = R.coordinate 1 := by
    apply mul_right_cancel₀ hpositive.ne'
    rw [← wall_homogeneous hpositive.le, ← homogeneous h]
    exact same.trans (congrArg Complex.re at_radial).symm
  intro k slab
  rw [wall_homogeneous (hpositive.le.trans slab.1), coefficients, ← homogeneous k]
  exact (joined h ⟨le_rfl, within⟩ (congrArg Complex.re at_radial).symm k slab).symm

end Unfoldings.ConvexRoof.SectorForest.GeometricSectorLeaf
