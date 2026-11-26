module

public import Unfoldings.Roof.GraphLensFaceAngles
public import Unfoldings.Roof.RestrictedBoundaryFrontier
public import Unfoldings.Geometry.GraphRegionSides

/-! The selected faces above an aligned graph have the actual local epigraph as their carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
  (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
  (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
  (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier) (graphPoint f '' Set.Icc a b))

local notation "Above" => facesAboveGraph sample f a b

include hf sample_in endpoints aligned

/-- Any interior point classifies its triangle the same way as the original sample. -/
theorem mem_facesAboveGraph_iff_of_interior (i : Face) {z : Plane}
    (inside : z ∈ interior (K.projectedTriangle i).carrier) :
    i ∈ Above ↔ z 0 ∈ Set.Ioo a b ∧ f (z 0) < z 1 :=
  aboveGraph_iff_of_cell hf (K.projectedTriangle i).convex_carrier.interior.isPreconnected
    (endpoints i) (aligned i) (sample_in i) inside

theorem selected_triangle_subset_closedAboveGraph (i : Face) (selected : i ∈ Above) :
    (K.projectedTriangle i).carrier ⊆ {z : Plane | z 0 ∈ Set.Icc a b ∧ f (z 0) ≤ z 1} := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  let y := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1
  have closed : IsClosed {z : Plane | z 0 ∈ Set.Icc a b ∧ f (z 0) ≤ z 1} :=
    (isClosed_Icc.preimage x.continuous).inter (isClosed_le (hf.comp x.continuous) y.continuous)
  let triangle := K.projectedTriangle i
  change triangle.carrier ⊆ _
  rw [← triangle.compact_carrier.isClosed.closure_eq,
    ← triangle.convex_carrier.closure_interior_eq_closure_of_nonempty_interior triangle.interior_nonempty]
  refine closure_minimal (fun z hz => ?_) closed
  obtain ⟨window, high⟩ :=
    (K.mem_facesAboveGraph_iff_of_interior hf sample sample_in endpoints aligned i hz).mp selected
  exact ⟨Set.Ioo_subset_Icc_self window, high.le⟩

private theorem mem_restrictedCarrier_of_strict_aboveGraph {z : Plane} (in_roof : z ∈ K.footprint)
    (window : z 0 ∈ Set.Ioo a b) (above : f (z 0) < z 1) :
    z ∈ K.restrictedCarrier Above := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  let y := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1
  let region := {p : Plane | p 0 ∈ Set.Ioo a b ∧ f (p 0) < p 1}
  have open_region : IsOpen region :=
    (isOpen_Ioo.preimage x.continuous).inter (isOpen_lt (hf.comp x.continuous) y.continuous)
  rw [K.footprint_eq_union_projectedTriangles] at in_roof
  obtain ⟨i, h⟩ := Set.mem_iUnion.mp in_roof
  let T := K.projectedTriangle i
  have close : z ∈ closure (interior T.carrier) := by
    rwa [T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
      T.compact_carrier.isClosed.closure_eq]
  obtain ⟨p, strict, in_T⟩ := mem_closure_iff_nhds.mp close region
    (open_region.mem_nhds (show z ∈ region from ⟨window, above⟩))
  have selected : i ∈ Above :=
    (K.mem_facesAboveGraph_iff_of_interior hf sample sample_in endpoints aligned i in_T).mpr strict
  exact Set.mem_iUnion.mpr ⟨⟨i, selected⟩, h⟩

/-- At any interior roof point strictly between the end lines, the geometric
carrier of the selected faces is exactly the closed upper side of the graph. -/
theorem mem_restrictedCarrier_aboveGraph_iff {z : Plane} (in_roof : z ∈ interior K.footprint)
    (window : z 0 ∈ Set.Ioo a b) :
    z ∈ K.restrictedCarrier Above ↔ f (z 0) ≤ z 1 := by
  constructor
  · intro member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact (K.selected_triangle_subset_closedAboveGraph hf sample sample_in endpoints aligned
      i.val i.property hi).2
  · intro above
    rw [← (K.compact_restrictedCarrier Above).isClosed.closure_eq]
    apply mem_closure_iff_nhds'.mpr
    intro N near
    let lift (t : ℝ) : Plane := WithLp.toLp 2 ![z 0, z 1 + t]
    have base : lift 0 = z := by
      ext k
      fin_cases k
      · rfl
      · change z 1 + 0 = z 1
        exact add_zero _
    have cont : Continuous lift := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro k
      fin_cases k
      · exact continuous_const
      · exact continuous_const.add continuous_id
    have within : lift ⁻¹' (N ∩ interior K.footprint) ∈ 𝓝 0 := by
      apply cont.continuousAt.preimage_mem_nhds
      rw [base]
      exact inter_mem near (isOpen_interior.mem_nhds in_roof)
    obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.mp within
    let t := ε / 2
    have t_pos : 0 < t := half_pos ε_pos
    have t_near : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos t_pos]
      exact half_lt_self ε_pos
    have h : lift t ∈ N ∩ interior K.footprint := hε t_near
    refine ⟨⟨lift t, K.mem_restrictedCarrier_of_strict_aboveGraph hf sample sample_in
      endpoints aligned (interior_subset h.2) window ?_⟩, h.1⟩
    change f (z 0) < z 1 + t
    exact above.trans_lt (lt_add_of_pos_right _ t_pos)

/-- Strictly above the graph, every incident corner belongs to the selected region. -/
theorem fullStarIn_facesAboveGraph {w : C.Vertex Set.univ}
    (window : K.projectedVertex w 0 ∈ Set.Ioo a b)
    (above : f (K.projectedVertex w 0) < K.projectedVertex w 1) :
    C.FullStarIn Above w := by
  intro c at_w
  let p := K.projectedVertex w
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  let y := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1
  let region := {z : Plane | z 0 ∈ Set.Ioo a b ∧ f (z 0) < z 1}
  have open_region : IsOpen region :=
    (isOpen_Ioo.preimage x.continuous).inter (isOpen_lt (hf.comp x.continuous) y.continuous)
  let T := K.projectedTriangle c.1
  have hp : p ∈ T.carrier := by
    dsimp only [p, T]
    rw [← at_w, K.projectedVertex_ofCorner]
    exact (K.projectedTriangle c.1).vertex_mem c.2
  have close : p ∈ closure (interior T.carrier) := by
    rwa [T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
      T.compact_carrier.isClosed.closure_eq]
  obtain ⟨z, hz, in_T⟩ := mem_closure_iff_nhds.mp close region
    (open_region.mem_nhds (show p ∈ region from ⟨window, above⟩))
  exact (K.mem_facesAboveGraph_iff_of_interior hf sample sample_in endpoints aligned c.1 in_T).mpr hz

/-- Strictly below the graph, the selected region contributes no incident angles. -/
theorem regionalAngleExcess_facesAboveGraph_of_below {w : C.Vertex Set.univ}
    (below : K.projectedVertex w 1 < f (K.projectedVertex w 0)) :
    K.regionalAngleExcess Above w = 0 := by
  classical
  unfold regionalAngleExcess TriangleComplex.regionalCornerSum
  apply Finset.sum_eq_zero
  intro c _
  apply ite_eq_right
  rintro ⟨selected, at_w⟩
  have position : K.projectedVertex w ∈ (K.projectedTriangle c.1).carrier := by
    rw [← at_w, K.projectedVertex_ofCorner]
    exact (K.projectedTriangle c.1).vertex_mem c.2
  exact (not_le_of_gt below) ((K.selected_triangle_subset_closedAboveGraph hf sample sample_in
    endpoints aligned c.1 selected position).2)

/-- On the strict upper side, an interior vertex contributes its full intrinsic defect. -/
theorem regionalAngleExcess_facesAboveGraph_of_above {w : C.Vertex Set.univ}
    (in_roof : K.projectedVertex w ∈ interior K.footprint)
    (window : K.projectedVertex w 0 ∈ Set.Ioo a b)
    (above : f (K.projectedVertex w 0) < K.projectedVertex w 1) :
    K.regionalAngleExcess Above w = -C.interiorAngularDefect Set.univ w := by
  classical
  have full := K.fullStarIn_facesAboveGraph hf sample sample_in endpoints aligned window above
  rw [regionalAngleExcess, C.regionalCornerSum_of_fullStar Above _ w full]
  have internal := (K.projectedVertex_mem_interior_iff w).mp in_roof
  simp only [TriangleComplex.interiorAngularDefect, ite_eq_right internal,
    ← K.projectedTotalAngle_eq_two_pi w internal, TriangleComplex.totalAngle, projectedTotalAngle,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases same : C.vertexOfCorner Set.univ c = w <;> simp [same]

theorem eventually_restrictedCarrier_aboveGraph {p : Plane} (inside : p ∈ interior K.footprint)
    (window : p 0 ∈ Set.Ioo a b) :
    ∀ᶠ z in 𝓝 p, z ∈ K.restrictedCarrier Above ↔ f (z 0) ≤ z 1 := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  filter_upwards [isOpen_interior.mem_nhds inside,
    (isOpen_Ioo.preimage x.continuous).mem_nhds window] with z in_roof in_window
  exact K.mem_restrictedCarrier_aboveGraph_iff hf sample sample_in endpoints aligned in_roof in_window

end Unfoldings.ConvexRoof
