module

public import Unfoldings.Polyhedron.TriangulationEuler
public import Unfoldings.Complex.SeamGraph
public import Unfoldings.Complex.Connectivity
public import Unfoldings.Combinatorics.DualComponentCount
public import Unfoldings.Development.NetPartition
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod

/-! Primal cut cycles count the components of the original triangle adjacency graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open scoped BigOperators

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

private theorem reachable_endpointGraph_of_edge {V E : Type*} (source target : E → V) (e : E) :
    (endpointGraph source target).Reachable (source e) (target e) := by
  by_cases loop : source e = target e
  · rw [loop]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨loop, Or.inl ⟨e, rfl, rfl⟩⟩)

private theorem card_components_eq_one_of_reachable {V : Type*} [Nonempty V]
    (G : SimpleGraph V) (connected : ∀ u v, G.Reachable u v) :
    Nat.card G.ConnectedComponent = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨?_⟩, inferInstance⟩
  intro c d
  obtain ⟨u, rfl⟩ := c.exists_rep
  obtain ⟨v, rfl⟩ := d.exists_rep
  exact SimpleGraph.ConnectedComponent.sound (connected u v)

include P in
theorem original_faces_reachable (f g : Face) :
    (endpointGraph (fun s => (C.left s).face) (fun s => (C.right s).face)).Reachable f g := by
  let := P.connectedSpace
  have related := C.duallyConnected_of_preconnected Set.univ f g
  induction related with
  | rel u v edge =>
    obtain ⟨s, _, rfl, rfl⟩ := edge
    exact reachable_endpointGraph_of_edge _ _ s
  | refl f => exact ⟨.nil⟩
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

include P in
private theorem all_vertices_reachable (v w : C.Vertex Set.univ) :
    (endpointGraph (C.seamVertex · false) (C.seamVertex · true)).Reachable v w := by
  let G := endpointGraph (C.seamVertex · false) (C.seamVertex · true)
  have along_edge {x y : C.Vertex Set.univ} (s : C.Seam) (h : C.seamGraph.IsLink s x y) :
      G.Reachable x y := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact reachable_endpointGraph_of_edge _ _ s
    · exact (reachable_endpointGraph_of_edge (C.seamVertex · false) (C.seamVertex · true) s).symm
  have along_local_edge (f : Face) (i : Fin 3) :
      G.Reachable (C.vertexOfCorner Set.univ (f, i))
        (C.vertexOfCorner Set.univ (f, Triangle.next i)) := by
    obtain ⟨s, h⟩ := C.exists_seamGraph_link_of_not_boundary ⟨f, i⟩
      (P.not_isBoundaryEdge ⟨f, i⟩)
    exact along_edge s h
  have in_face (f : Face) (i : Fin 3) :
      G.Reachable (C.vertexOfCorner Set.univ (f, 0)) (C.vertexOfCorner Set.univ (f, i)) := by
    fin_cases i
    · exact ⟨.nil⟩
    · exact along_local_edge f 0
    · exact (along_local_edge f 2).symm
  have across (s : C.Seam) :
      G.Reachable (C.vertexOfCorner Set.univ ((C.left s).face, 0))
        (C.vertexOfCorner Set.univ ((C.right s).face, 0)) := by
    let l := C.germOfEndpoint (C.left s) false
    let r := C.germOfEndpoint (C.right s) (C.acrossEndpoint s false false)
    have crosses : C.GermCrosses Set.univ l r := ⟨s, Set.mem_univ _, false, false, rfl, rfl⟩
    have eq := crosses.vertex_eq
    exact (in_face (C.left s).face l.1.2).trans
      (eq ▸ (in_face (C.right s).face r.1.2).symm)
  obtain ⟨⟨f, i⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ v
  obtain ⟨⟨g, j⟩, rfl⟩ := C.vertexOfCorner_surjective Set.univ w
  have walk := P.original_faces_reachable f g
  have faces : G.Reachable (C.vertexOfCorner Set.univ (f, 0))
      (C.vertexOfCorner Set.univ (g, 0)) := by
    obtain ⟨walk⟩ := walk
    induction walk with
    | nil => exact ⟨.nil⟩
    | cons edge _ ih =>
      apply SimpleGraph.Reachable.trans _ ih
      rcases ((SimpleGraph.fromRel_adj _ _ _).mp edge).2 with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩
      · exact across s
      · exact (across s).symm
  exact (in_face f i).symm.trans (faces.trans (in_face g j))

include P in
private theorem triangle_boundary_is_cycle (x : Face → ZMod 2) :
    edgeCoboundary (fun s => (C.left s).face) (fun s => (C.right s).face) (ZMod 2) x ∈
      coordinateCycleSpace (C.seamVertex · false) (C.seamVertex · true) := by
  apply (mem_coordinateCycleSpace _ _ _).mpr
  intro y
  let atCorner (f : Face) (i : Fin 3) := y (C.vertexOfCorner Set.univ (f, i))
  let edgeTerm (p : Face × Fin 3) :=
    x p.1 * (atCorner p.1 p.2 + atCorner p.1 (Triangle.next p.2))
  have endpoint_sum (s : C.Seam) (b : Bool) :
      atCorner (C.seamSide s b).face (C.seamSide s b).edge +
        atCorner (C.seamSide s b).face (Triangle.next (C.seamSide s b).edge) =
      y (C.seamVertex s true) + y (C.seamVertex s false) := by
    have link := C.seamGraph_side_link s b
    change (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _) at link
    change y (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s b) false).1) +
      y (C.vertexOfCorner Set.univ (C.germOfEndpoint (C.seamSide s b) true).1) = _
    rcases link with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂, add_comm]
    · rw [h₁, h₂]
  simp only [edgeCoboundary_apply, CharTwo.sub_eq_add]
  calc
    _ = ∑ p : C.Seam × Bool, edgeTerm (P.seamSideEquiv p) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      have bools : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [bools]
      simp only [Finset.sum_insert (by decide : false ∉ ({true} : Finset Bool)),
        Finset.sum_singleton]
      change (_ + _) * _ =
        x (C.seamSide s false).face *
            (atCorner (C.seamSide s false).face (C.seamSide s false).edge +
              atCorner (C.seamSide s false).face (Triangle.next (C.seamSide s false).edge)) +
          x (C.seamSide s true).face *
            (atCorner (C.seamSide s true).face (C.seamSide s true).edge +
              atCorner (C.seamSide s true).face (Triangle.next (C.seamSide s true).edge))
      rw [endpoint_sum s false, endpoint_sum s true, add_mul]
      exact add_comm _ _
    _ = ∑ p : Face × Fin 3, edgeTerm p := Equiv.sum_comp P.seamSideEquiv edgeTerm
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro f _
      change (∑ i : Fin 3, x f * (atCorner f i + atCorner f (Triangle.next i))) = 0
      rw [← Finset.mul_sum, Fin.sum_univ_three]
      change x f * ((atCorner f 0 + atCorner f 1) + (atCorner f 1 + atCorner f 2) +
        (atCorner f 2 + atCorner f 0)) = 0
      have pair :
          (atCorner f 0 + atCorner f 1) + (atCorner f 1 + atCorner f 2) +
            (atCorner f 2 + atCorner f 0) =
          (atCorner f 0 + atCorner f 0) + (atCorner f 1 + atCorner f 1) +
            (atCorner f 2 + atCorner f 2) := by ac_rfl
      rw [pair]
      simp [CharTwo.add_self_eq_zero]

include P in
/-- On the original triangulation, all primal cycles over the field of two
elements are boundaries of triangle chains. -/
theorem original_seam_cycle_exactness :
    LinearMap.range
        (edgeCoboundary (fun s => (C.left s).face) (fun s => (C.right s).face) (ZMod 2)) =
      coordinateCycleSpace (K := ZMod 2) (C.seamVertex · false) (C.seamVertex · true) := by
  let := P.connectedSpace
  have nonempty_total : Nonempty C.Total := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (C.Realization Set.univ))
    obtain ⟨a, _⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
    exact ⟨a⟩
  let : Nonempty Face := nonempty_total.map Sigma.fst
  let : Nonempty (C.Vertex Set.univ) :=
    (inferInstance : Nonempty Face).map fun f => C.vertexOfCorner Set.univ (f, 0)
  refine range_edgeCoboundary_eq_coordinateCycleSpace _ _ _ _
    (card_components_eq_one_of_reachable _ P.all_vertices_reachable)
    (card_components_eq_one_of_reachable _ P.original_faces_reachable) P.triangulation_euler ?_
  rintro _ ⟨x, rfl⟩
  exact P.triangle_boundary_is_cycle x


/-- The primal cut graph includes every original vertex, even if it is not on a cut. -/
def labelCutGraph {L : Type*} (label : Face → L) : SimpleGraph (C.Vertex Set.univ) :=
  endpointGraph
    (fun s : {s : C.Seam // label (C.left s).face ≠ label (C.right s).face} =>
      C.seamVertex s.val false)
    (fun s => C.seamVertex s.val true)

open Classical in
include P in
/-- The number of same-label triangle components is one plus the cycle rank
of the graph of all original seams whose incident labels differ. -/
theorem labeled_components_eq_cut_cycle_rank {L : Type*} (label : Face → L) :
    Nat.card (C.labeledSeamGraph label).ConnectedComponent + Fintype.card (C.Vertex Set.univ) =
      1 + Fintype.card {s : C.Seam // label (C.left s).face ≠ label (C.right s).face} +
        Nat.card (labelCutGraph (C := C) label).ConnectedComponent := by
  let cut (s : C.Seam) := label (C.left s).face ≠ label (C.right s).face
  let l (s : C.Seam) := (C.left s).face
  let r (s : C.Seam) := (C.right s).face
  let b (s : C.Seam) := C.seamVertex s false
  let e (s : C.Seam) := C.seamVertex s true
  have held : endpointGraph (l ∘ (Subtype.val : {s // ¬ cut s} → C.Seam))
      (r ∘ Subtype.val) = C.labeledSeamGraph label := by
    ext f g
    change (SimpleGraph.fromRel _).Adj f g ↔ _
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨ne, ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩⟩
      · exact ⟨ne, not_not.mp s.property, s.val, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨ne, (not_not.mp s.property).symm, s.val, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨ne, same, s, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · exact ⟨ne, Or.inl ⟨⟨s, by simpa only [cut, h₁, h₂] using not_not.mpr same⟩, h₁, h₂⟩⟩
      · exact ⟨ne, Or.inr ⟨⟨s, by simpa only [cut, h₁, h₂] using not_not.mpr same.symm⟩, h₁, h₂⟩⟩
  let : Nonempty Face := by
    let := P.connectedSpace
    obtain ⟨x⟩ := (inferInstance : Nonempty (C.Realization Set.univ))
    obtain ⟨a, _⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
    exact ⟨a.1⟩
  have one : Nat.card (endpointGraph l r).ConnectedComponent = 1 :=
    card_components_eq_one_of_reachable _ P.original_faces_reachable
  have components := dual_components_eq_cut_cycle_rank b e l r cut P.original_seam_cycle_exactness
  rw [held, one] at components
  have rank := finrank_coordinateCycleSpace_add_card_vertex (K := ZMod 2)
    (b ∘ (Subtype.val : {s // cut s} → C.Seam)) (e ∘ Subtype.val)
  change _ + _ = _ + Nat.card (labelCutGraph (C := C) label).ConnectedComponent at rank
  change _ + _ = 1 + Fintype.card {s // cut s} + _
  omega

end Unfoldings.SpatialFolding.ConvexBoundary
