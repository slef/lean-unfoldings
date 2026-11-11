module

public import Unfoldings.Geometry.ConstrainedEdgeSubdivision

/-! Exact finite whole-edge coverage of every old edge respected by supporting-line constraints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleFamily

variable {I : Type*} [Finite I] (triangle : I → Triangle)

/-- Respecting all three supporting lines subdivides an old edge exactly into whole fine edges. -/
theorem edge_eq_union_subedges (U : Triangle) (e : Fin 3)
    (cover : U.edge e ⊆ ⋃ i, (triangle i).carrier)
    (signs : I → Fin 3 → Bool)
    (side : ∀ i k p, p ∈ (triangle i).carrier →
      0 ≤ AffineArrangement.signed (U.coord k) (signs i k) p) :
    U.edge e = ⋃ a : {a : I × Fin 3 // (triangle a.1).edge a.2 ⊆ U.edge e},
      (triangle a.val.1).edge a.val.2 := by
  classical
  let E := {a : I × Fin 3 // (triangle a.1).edge a.2 ⊆ U.edge e}
  let edges : Set Plane := ⋃ a : E, (triangle a.val.1).edge a.val.2
  have closed_edges : IsClosed edges := isClosed_iUnion_of_finite
    (fun a => (triangle a.val.1).compact_edge a.val.2 |>.isClosed)
  have subset : edges ⊆ U.edge e := Set.iUnion_subset (fun a => a.property)
  have vertices_finite : {x : U.Edge e | ∃ i, (triangle i).IsVertex x.val}.Finite := by
    apply (Set.finite_range (fun a : I × Fin 3 => (triangle a.1).vertex a.2)).of_injOn
      (f := fun x : U.Edge e => x.val) _ Subtype.val_injective.injOn
    rintro x ⟨i, k, equal⟩
    exact ⟨(i, k), equal⟩
  apply Set.Subset.antisymm _ subset
  intro p member
  by_contra absent
  let x : U.Edge e := ⟨p, member⟩
  let neighborhood : Set (U.Edge e) := Subtype.val ⁻¹' edgesᶜ
  have open_neighborhood : IsOpen neighborhood :=
    closed_edges.isOpen_compl.preimage continuous_subtype_val
  have inside : x ∈ neighborhood := absent
  let := U.edgePerfectSpace e
  have infinite := infinite_of_mem_nhds x (open_neighborhood.mem_nhds inside)
  apply infinite
  apply vertices_finite.subset
  intro y outside
  obtain ⟨i, in_triangle⟩ := Set.mem_iUnion.mp (cover y.property)
  refine ⟨i, ?_⟩
  by_contra regular
  obtain ⟨f, on_edge, contained⟩ := U.exists_subedge_of_signed_coords (triangle i) (signs i)
    (side i) e y.property in_triangle regular
  exact outside (Set.mem_iUnion.mpr ⟨⟨(i, f), contained⟩, on_edge⟩)

end Unfoldings.TriangleFamily
