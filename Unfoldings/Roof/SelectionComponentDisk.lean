module

public import Unfoldings.Roof.SelectionInteriorLabels
public import Unfoldings.Topology.JordanFilling

/-! Every whole-edge component of a convex-gradient roof selection is a Jordan disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
theorem selectionComponent_carrier_subset {slopes : Set Plane} {seed : Face}
    (selected : K.normalSlope seed ∈ slopes) :
    K.restrictedCarrier (K.selectionComponent slopes seed) ⊆ K.selectedCarrier slopes := by
  intro p member
  obtain ⟨f, in_face⟩ := Set.mem_iUnion.mp member
  exact K.mem_selectedCarrier.mpr
    ⟨f.val, K.selectionComponent_selected selected f.property, in_face⟩

open Classical in
/-- Every nonempty whole-edge component of a closed convex gradient selection has a simple
Jordan frontier. Other selected components may touch it at original vertices. -/
theorem selectionComponent_frontier_isJordan {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (seed : Face)
    (selected : K.normalSlope seed ∈ slopes) :
    Schoenflies.IsJordanCurve
      (frontier (K.restrictedCarrier (K.selectionComponent slopes seed))) := by
  let U := K.selectionComponent slopes seed
  let S := K.restrictedCarrier U
  obtain ⟨bank⟩ := K.exists_restricted_bank U ⟨seed, K.seed_mem_selectionComponent slopes seed⟩
  obtain ⟨J, jordan, on_banks⟩ := K.exists_restricted_boundary_Jordan U bank
  have boundary : J ⊆ frontier S :=
    on_banks.trans (K.restricted_boundary_subset_frontier U)
  have inside_global : Schoenflies.inside J ⊆ K.selectedCarrier slopes :=
    K.inside_subset_selectedCarrier convex closed ⟨K.normalSlope seed, selected⟩
      (boundary.trans ((K.compact_restrictedCarrier U).isClosed.frontier_subset.trans
        (K.selectionComponent_carrier_subset selected)))
  have separation := Schoenflies.jordan_curve_theorem jordan
  have inside_interior : Schoenflies.inside J ⊆ interior (K.selectedCarrier slopes) :=
    separation.isOpen_inside.subset_interior_iff.mpr inside_global
  obtain ⟨q, in_q⟩ := separation.isConnected_inside.nonempty
  obtain ⟨g, selected_g, q_in_g⟩ := K.mem_selectedCarrier.mp (inside_global in_q)
  have inside_other := K.region_subset_selectionComponent
    separation.isConnected_inside.isPreconnected inside_interior g ⟨q, in_q, q_in_g⟩
  have boundary_other : J ⊆ K.restrictedCarrier (K.selectionComponent slopes g) := by
    have in_closure : J ⊆ closure (Schoenflies.inside J) :=
      separation.frontier_inside.symm.subset.trans frontier_subset_closure
    exact in_closure.trans (closure_minimal inside_other
      (K.compact_restrictedCarrier _).isClosed)
  obtain ⟨p, in_J, omitted⟩ := PlanarTopology.exists_Jordan_point_not_mem_countable jordan
    (Set.finite_range (fun fi : Face × Fin 3 => (K.projectedTriangle fi.1).vertex fi.2)).countable
  obtain ⟨y, in_bank, image⟩ := on_banks in_J
  obtain ⟨edge, x, rfl⟩ := Set.mem_iUnion.mp in_bank
  change K.projectFace edge.val.face.val x.val = p at image
  obtain ⟨h, in_h⟩ := Set.mem_iUnion.mp (boundary_other in_J)
  rw [projectedTriangle, Triangle.affineImage_carrier] at in_h
  obtain ⟨z, hz, last⟩ := in_h
  let a : C.Total := ⟨edge.val.face.val, ⟨x.val, x.property |> (C.triangle _).edge_subset _⟩⟩
  let b : C.Total := ⟨h.val, ⟨z, hz⟩⟩
  have regular : ¬ C.IsVertex a := by
    rintro ⟨i, at_corner⟩
    apply omitted
    exact ⟨(edge.val.face.val, i), (congrArg (K.projectFace _) at_corner).trans image⟩
  have labels := K.selection_label_eq_of_regular_contact (a := a) (b := b)
    (K.selectionComponent_selected selected edge.val.face.property)
    (K.selectionComponent_selected selected_g h.property) regular (image.trans last.symm)
  have first_label : (K.selectionGraph slopes).connectedComponentMk edge.val.face.val =
      (K.selectionGraph slopes).connectedComponentMk seed := edge.val.face.property
  have last_label : (K.selectionGraph slopes).connectedComponentMk h.val =
      (K.selectionGraph slopes).connectedComponentMk g := h.property
  have roots := first_label.symm.trans (labels.trans last_label)
  have same_component : K.selectionComponent slopes g = U := by
    dsimp [selectionComponent, U]
    rw [roots]
  have filled : Schoenflies.inside J ⊆ S := by
    rwa [same_component] at inside_other
  have regular_set := TriangleFamily.closure_interior_union
    (fun f : {f : Face // f ∈ U} => K.projectedTriangle f.val)
  have frontier_equal := PlanarTopology.frontier_eq_of_filled_Jordan_frontier_subset
    (K.compact_restrictedCarrier U) regular_set
    (K.isConnected_interior_selectionComponent slopes seed)
    jordan boundary filled
  change Schoenflies.IsJordanCurve (frontier S)
  rw [frontier_equal]
  exact jordan

open Classical in
/-- The actual geometric union of each whole-edge selection component is a closed disk. -/
theorem exists_selectionComponent_disk {slopes : Set Plane}
    (convex : Convex ℝ slopes) (closed : IsClosed slopes) (seed : Face)
    (selected : K.normalSlope seed ∈ slopes) :
    Nonempty (K.restrictedCarrier (K.selectionComponent slopes seed) ≃ₜ
      Metric.closedBall (0 : Plane) 1) :=
  PlanarTopology.exists_diskHomeomorph_of_compact_Jordan_frontier
    (K.compact_restrictedCarrier _) (K.isConnected_interior_selectionComponent slopes seed).nonempty
    (K.selectionComponent_frontier_isJordan convex closed seed selected)

end Unfoldings.ConvexRoof
