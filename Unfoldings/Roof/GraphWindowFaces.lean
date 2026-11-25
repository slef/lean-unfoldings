module

public import Unfoldings.Roof.AboveGraphBankEnds
public import Unfoldings.Geometry.GraphWindowSide

/-! In a coarse graph window, the region upper fans have the actual epigraph as their local carrier. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Select the coarse faces by the side of their interiors within the open window. -/
def graphWindowFaces (f : ℝ → ℝ) (a b : ℝ) : Set Face :=
  {j | interiorAboveGraph f a b (K.projectedTriangle j).carrier}

variable {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
  (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))

local notation "U" => K.graphWindowFaces f a b
local notation "X" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
local notation "Y" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1

include hf aligned in
/-- Any strict interior point in the window determines its original face's side. -/
theorem mem_graphWindowFaces_iff (j : Face) {z : Plane}
    (inside : z ∈ interior (K.projectedTriangle j).carrier) (window : z 0 ∈ Set.Ioo a b) :
    j ∈ (U) ↔ f (z 0) < z 1 :=
  interiorAboveGraph_iff_of_mem_window hf (K.projectedTriangle j).convex_carrier (aligned j) inside window

include hf aligned in
private theorem graphWindow_selected_above (j : Face) (selected : j ∈ (U)) {z : Plane}
    (member : z ∈ (K.projectedTriangle j).carrier) (window : z 0 ∈ Set.Ioo a b) :
    f (z 0) ≤ z 1 := by
  by_contra! below
  let T := K.projectedTriangle j
  let V := {p : Plane | p 0 ∈ Set.Ioo a b ∧ p 1 < f (p 0)}
  have open_V : IsOpen V := (isOpen_Ioo.preimage (X).continuous).inter
    (isOpen_lt (Y).continuous (hf.comp (X).continuous))
  have close : z ∈ closure (interior T.carrier) := by
    rw [T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
    exact subset_closure member
  obtain ⟨p, ⟨within, lower⟩, inside⟩ :=
    mem_closure_iff_nhds.mp close V (open_V.mem_nhds ⟨window, below⟩)
  exact lower.not_gt ((K.mem_graphWindowFaces_iff hf aligned j inside within).mp selected)

include hf in
private theorem mem_graphWindowCarrier_of_above {z : Plane}
    (in_roof : z ∈ K.footprint) (window : z 0 ∈ Set.Ioo a b) (above : f (z 0) < z 1) :
    z ∈ K.restrictedCarrier (U) := by
  rw [K.footprint_eq_union_projectedTriangles] at in_roof
  obtain ⟨j, member⟩ := Set.mem_iUnion.mp in_roof
  let T := K.projectedTriangle j
  let V := {p : Plane | p 0 ∈ Set.Ioo a b ∧ f (p 0) < p 1}
  have open_V : IsOpen V := (isOpen_Ioo.preimage (X).continuous).inter
    (isOpen_lt (hf.comp (X).continuous) (Y).continuous)
  have close : z ∈ closure (interior T.carrier) := by
    rw [T.convex_carrier.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
    exact subset_closure member
  obtain ⟨p, hp, interior⟩ := mem_closure_iff_nhds.mp close V (open_V.mem_nhds ⟨window, above⟩)
  exact Set.mem_iUnion.mpr ⟨⟨j, ⟨p, interior, hp⟩⟩, member⟩

include hf aligned in
/-- The closed upper side agrees locally with the carrier of the selected coarse faces. -/
theorem mem_restrictedCarrier_graphWindow_iff {z : Plane}
    (in_roof : z ∈ interior K.footprint) (window : z 0 ∈ Set.Ioo a b) :
    z ∈ K.restrictedCarrier (U) ↔ f (z 0) ≤ z 1 := by
  constructor
  · intro member
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp member
    exact K.graphWindow_selected_above hf aligned j.val j.property hj window
  · intro above
    rw [← (K.compact_restrictedCarrier (U)).isClosed.closure_eq]
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
    obtain ⟨r, r_pos, h_r⟩ := Metric.mem_nhds_iff.mp within
    have close : r / 2 ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos r_pos)]
      exact half_lt_self r_pos
    have h := h_r close
    refine ⟨⟨lift (r / 2), K.mem_graphWindowCarrier_of_above hf (interior_subset h.2) window ?_⟩, h.1⟩
    change f (z 0) < z 1 + r / 2
    exact above.trans_lt (lt_add_of_pos_right _ (half_pos r_pos))

include hf aligned in
theorem eventually_restrictedCarrier_graphWindow {z : Plane}
    (in_roof : z ∈ interior K.footprint) (window : z 0 ∈ Set.Ioo a b) :
    ∀ᶠ p in 𝓝 z, p ∈ K.restrictedCarrier (U) ↔ f (p 0) ≤ p 1 := by
  filter_upwards [isOpen_interior.mem_nhds in_roof,
    (isOpen_Ioo.preimage (X).continuous).mem_nhds window] with p hp time
  exact K.mem_restrictedCarrier_graphWindow_iff hf aligned hp time

include hf aligned in
open Classical in
/-- The whole upper fan at an interior graph contact has a unique intrinsic vertex copy. -/
theorem graphWindow_vertex_unique {z : Plane}
    (in_roof : z ∈ interior K.footprint) (window : z 0 ∈ Set.Ioo a b) (on_graph : z 1 = f (z 0))
    (v w : (C.restrictFaces (U)).Vertex Set.univ)
    (at_v : K.projectedVertex (C.includeRestrictedVertexUniv (U) v) = z)
    (at_w : K.projectedVertex (C.includeRestrictedVertexUniv (U) w) = z) :
    v = w :=
  K.restricted_vertex_eq_of_punctured_neighborhood (U)
    (fun _ positive => exists_punctured_epigraph_neighborhood hf on_graph
      (K.eventually_restrictedCarrier_graphWindow hf aligned in_roof window) positive)
    v w at_v at_w

end Unfoldings.ConvexRoof
