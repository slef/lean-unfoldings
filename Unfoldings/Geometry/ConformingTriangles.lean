module

public import Unfoldings.Geometry.SharedEdgeOpening
public import Unfoldings.Geometry.HingePatch
public import Mathlib.Topology.Separation.Connected

/-! Face-to-face conformity, including exact closed intersections. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

/-- Equal whole edges and disjoint interiors determine the entire closed intersection. -/
theorem inter_eq_shared_edge (T U : Triangle) (e f : Fin 3) (same : T.edge e = U.edge f)
    (separated : Disjoint (interior T.carrier) (interior U.carrier)) :
    T.carrier ∩ U.carrier = T.edge e := by
  let H : HingePlacement T U e f (T.sharedEdgeIdentification U e f same) :=
    { place := AffineIsometryEquiv.refl ℝ Plane
      joined := fun _ => rfl
      opposite := T.opposite_of_shared_edge U e f same separated }
  simpa only [H, AffineIsometryEquiv.coe_refl, Set.image_id] using H.inter_eq_edge

end Unfoldings.Triangle

namespace Unfoldings.TriangleFamily

variable {I : Type*} (triangle : I → Triangle)

/-- At a contact, both triangles have a vertex there or they share a whole edge through it. -/
def Conforming : Prop := ∀ i j, i ≠ j → ∀ p ∈ (triangle i).carrier ∩ (triangle j).carrier,
  ((triangle i).IsVertex p ∧ (triangle j).IsVertex p) ∨
    ∃ e f : Fin 3, (triangle i).edge e = (triangle j).edge f ∧ p ∈ (triangle i).edge e

/-- A conforming partition has only empty, common-vertex, or common-whole-edge intersections. -/
theorem Conforming.intersection_cases (conforming : Conforming triangle)
    (separated : Pairwise (fun i j =>
      Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)))
    {i j : I} (different : i ≠ j) :
    (triangle i).carrier ∩ (triangle j).carrier = ∅ ∨
      (∃ p, (triangle i).IsVertex p ∧ (triangle j).IsVertex p ∧
        (triangle i).carrier ∩ (triangle j).carrier = {p}) ∨
      ∃ e f : Fin 3, (triangle i).edge e = (triangle j).edge f ∧
        (triangle i).carrier ∩ (triangle j).carrier = (triangle i).edge e := by
  classical
  by_cases shared : ∃ e f : Fin 3, (triangle i).edge e = (triangle j).edge f
  · obtain ⟨e, f, equal⟩ := shared
    exact Or.inr (Or.inr ⟨e, f, equal,
      (triangle i).inter_eq_shared_edge (triangle j) e f equal (separated different)⟩)
  · have all_vertices : (triangle i).carrier ∩ (triangle j).carrier ⊆
        Set.range (triangle i).vertex := by
      intro p member
      rcases conforming i j different p member with vertices | ⟨e, f, equal, _⟩
      · exact vertices.1
      · exact (shared ⟨e, f, equal⟩).elim
    have finite := (Set.finite_range (triangle i).vertex).subset all_vertices
    have connected := ((triangle i).convex_carrier.inter (triangle j).convex_carrier).isPreconnected
    have subsingleton : ((triangle i).carrier ∩ (triangle j).carrier).Subsingleton := by
      by_contra nontrivial
      exact (connected.infinite_of_nontrivial (Set.not_subsingleton_iff.mp nontrivial)) finite
    by_cases empty : (triangle i).carrier ∩ (triangle j).carrier = ∅
    · exact Or.inl empty
    · obtain ⟨p, member⟩ := Set.nonempty_iff_ne_empty.mpr empty
      have vertices := conforming i j different p member
      rcases vertices with vertices | ⟨e, f, equal, _⟩
      · exact Or.inr (Or.inl ⟨p, vertices.1, vertices.2,
          Set.ext (fun x => ⟨fun hx => subsingleton hx member,
            fun hx => (Set.mem_singleton_iff.mp hx) ▸ member⟩)⟩)
      · exact (shared ⟨e, f, equal⟩).elim

end Unfoldings.TriangleFamily
