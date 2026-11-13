module

public import Unfoldings.Roof.ProjectedOpening
public import Unfoldings.Roof.RestrictedBoundaryFrontier
public import Unfoldings.Topology.JordanBoundarySubset
public import Unfoldings.Geometry.HingePatch

/-! Every nonempty whole-face roof restriction has an actual unpaired bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- A nonvertex frontier point of a whole-face restriction lies on an unpaired original edge. -/
theorem exists_restricted_bank_of_regular_frontier (U : Set Face) {p : Plane}
    (boundary : p ∈ frontier (K.restrictedCarrier U))
    (regular : ∀ f i, p ≠ (K.projectedTriangle f).vertex i) :
    Nonempty ((C.restrictFaces U).BoundaryBank Set.univ) := by
  let R := C.restrictFaces U
  have member := (K.compact_restrictedCarrier U).isClosed.frontier_subset boundary
  obtain ⟨f, in_face⟩ := Set.mem_iUnion.mp member
  have not_interior : p ∉ interior (K.projectedTriangle f.val).carrier := by
    intro inside
    exact boundary.2
      (interior_mono (Set.subset_iUnion (fun f : {f : Face // f ∈ U} =>
        (K.projectedTriangle f.val).carrier) f) inside)
  obtain ⟨e, on_edge⟩ := (K.projectedTriangle f.val).exists_edge_of_not_mem_interior
    ⟨p, in_face⟩ not_interior
  by_cases bank : R.IsBoundaryEdge Set.univ ⟨f, e⟩
  · exact ⟨⟨⟨f, e⟩, bank⟩⟩
  · obtain ⟨s, _, left | right⟩ := not_not.mp bank
    all_goals
      have same : (K.projectedTriangle (R.left s).face.val).edge (R.left s).edge =
          (K.projectedTriangle (R.right s).face.val).edge (R.right s).edge :=
        K.projected_seam_edges_eq s.val
      have first : p ∈ (K.projectedTriangle (R.left s).face.val).edge (R.left s).edge := by
        first
        | simpa only [← left] using on_edge
        | rw [same]; simpa only [← right] using on_edge
      let T := K.projectedTriangle (R.left s).face.val
      let V := K.projectedTriangle (R.right s).face.val
      let H : HingePlacement T V (R.left s).edge (R.right s).edge
          (T.sharedEdgeIdentification V (R.left s).edge (R.right s).edge same) :=
        { place := AffineIsometryEquiv.refl ℝ Plane
          joined := fun _ => rfl
          opposite := K.projected_opposite s.val }
      have not_vertex : ¬ T.IsVertex p := by
        rintro ⟨i, same⟩
        exact regular (R.left s).face.val i same.symm
      obtain ⟨r, positive, cover⟩ := H.exists_ball_cover ⟨p, first⟩ not_vertex
      have included : Metric.ball p r ⊆ K.restrictedCarrier U := by
        intro q hq
        have in_pair : q ∈ T.carrier ∪ V.carrier := by
          simpa only [H, AffineIsometryEquiv.coe_refl, Set.image_id] using cover hq
        rcases in_pair with a | b
        · exact Set.mem_iUnion.mpr ⟨(R.left s).face, a⟩
        · exact Set.mem_iUnion.mpr ⟨(R.right s).face, b⟩
      exact (boundary.2 (mem_interior_iff_mem_nhds.mpr
        (Metric.mem_nhds_iff.mpr ⟨r, positive, included⟩))).elim

include K in
open Classical in
/-- Every nonempty whole-face roof patch has a boundary bank; no disk hypothesis is used. -/
theorem exists_restricted_bank (U : Set Face) (nonempty : U.Nonempty) :
    Nonempty ((C.restrictFaces U).BoundaryBank Set.univ) := by
  let S := K.restrictedCarrier U
  let vertices := Set.range (fun fi : Face × Fin 3 => (K.projectedTriangle fi.1).vertex fi.2)
  obtain ⟨f, hf⟩ := nonempty
  have inside : (interior S).Nonempty :=
    (K.projectedTriangle f).interior_nonempty.mono
      (interior_mono (Set.subset_iUnion (fun f : {f : Face // f ∈ U} =>
        (K.projectedTriangle f.val).carrier) ⟨f, hf⟩))
  obtain ⟨base, outside, _⟩ :=
    Schoenflies.exists_unique_unbounded_connectedComponentIn_compl (K.compact_restrictedCarrier U)
  obtain ⟨p, boundary, omitted⟩ := PlanarTopology.exists_frontier_not_mem_countable
    (K.compact_restrictedCarrier U).isClosed inside ⟨base, outside⟩
    (Set.finite_range (fun fi : Face × Fin 3 => (K.projectedTriangle fi.1).vertex fi.2)).countable
  exact K.exists_restricted_bank_of_regular_frontier U boundary
    (fun f i equal => omitted ⟨(f, i), equal.symm⟩)

end Unfoldings.ConvexRoof
