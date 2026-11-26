module

public import Unfoldings.Roof.GraphRegionFaces
public import Unfoldings.Roof.ProjectedGermSegments
public import Unfoldings.Roof.HorizontalClosingEdges

/-! A restricted graph-side face has nonnegative outgoing transverse coordinate at a horizontal contact. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

set_option maxHeartbeats 800000 in
/-- The graph is locally horizontal at the start of the germ. Any selected
face containing the germ is on the upper side there. -/
theorem projectedGermRay_transverse_nonneg_of_above_horizontal {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
    (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier) (graphPoint f '' Set.Icc a b))
    {w : C.Vertex Set.univ} (g : C.LinkGerm Set.univ w)
    (selected : g.val.1.1 ∈ facesAboveGraph sample f a b)
    (horizontal : ∀ᶠ t in 𝓝 (K.projectedVertex w 0), f t = K.projectedVertex w 1) :
    0 ≤ K.projectedGermRay g 1 := by
  let p := K.projectedVertex w
  let d := K.projectedGermRay g
  let x (t : ℝ) := p + t • d
  have start : K.projectedGermStart g.val = p :=
    (K.projectedVertex_ofCorner g.val.1.1 g.val.1.2).symm.trans
      (congrArg K.projectedVertex g.property)
  have diff : d = K.projectedGermFinish g.val - K.projectedGermStart g.val := by
    rw [show d = Cap.horizontal (K.folding.germDirection g.val) from
      (K.horizontal_germDirection g).symm]
    rw [SpatialFolding.germDirection, map_sub]
    rfl
  have eq (t : ℝ) : x t = AffineMap.lineMap (K.projectedGermStart g.val) (K.projectedGermFinish g.val) t := by
    change p + t • d = _
    rw [AffineMap.lineMap_apply_module', diff, start, add_comm]
  have near : Tendsto (fun t : ℝ => x t 0) (𝓝[>] 0) (𝓝 (p 0)) := by
    have con : Continuous (fun t : ℝ => x t 0) := by unfold x; fun_prop
    have cont : ContinuousWithinAt (fun t : ℝ => x t 0) (Set.Ioi 0) 0 :=
      con.continuousAt.continuousWithinAt
    have x0 : x 0 0 = p 0 := by simp [x]
    exact x0 ▸ cont
  have good : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < 1 ∧ f (x t 0) = p 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1), near.eventually horizontal] with t ht h
    exact ⟨ht.1, ht.2, h⟩
  obtain ⟨t, tp, small, flat⟩ := good.exists
  have hit : x t ∈ (K.projectedTriangle g.val.1.1).carrier := by
    apply (K.projectedTriangle g.val.1.1).edge_subset (C.germEdge g.val).edge
    rw [← K.projectedGerm_segment_eq, eq]
    exact lineMap_mem_segment ℝ _ _ ⟨tp.le, small.le⟩
  have on := (K.selected_triangle_subset_closedAboveGraph hf sample sample_in endpoints aligned _ selected hit).2
  rw [flat] at on
  change p 1 ≤ p 1 + t * d 1 at on
  exact nonneg_of_mul_nonneg_right (by linarith only [on] : 0 ≤ t * d 1) tp

end Unfoldings.ConvexRoof
