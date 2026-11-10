module

public import Unfoldings.Polyhedron.CutDiskConverse
public import Unfoldings.Polyhedron.CutTree
public import Unfoldings.Complex.CollapsedCutCarrier

/-!
# The canonical primal cut graph is a tree exactly for cut disks

Both directions use one edge per actual cut seam and precisely the incident
original vertices. The necessity proof constructs that graph's embedding in
the uncut sphere. Loops and parallel edges are retained throughout the test.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem cutSeamGraph_tree_of_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) :
    (C.cutSeamGraph retain).IsTree := by
  let inclusion : retain ⊆ (Set.univ : Set C.Seam) := Set.subset_univ _
  have no_boundary (x : C.Realization Set.univ) : x ∉ C.bankBoundary Set.univ := by
    rintro boundary
    obtain ⟨bank, _point⟩ := Set.mem_iUnion.mp boundary
    exact P.not_isBoundaryEdge bank.val bank.property
  have no_root (v : C.Vertex Set.univ) : v ∉ C.relativeCutRoots Set.univ := by
    rintro ⟨edge, boundary, _which⟩
    exact P.not_isBoundaryEdge edge boundary
  let q : C(C.Realization Set.univ, C.Realization Set.univ) := ContinuousMap.id _
  have fibers : ∀ x y, q x = q y ↔
      x = y ∨ (x ∈ C.bankBoundary Set.univ ∧ y ∈ C.bankBoundary Set.univ) := by
    intro x y
    exact ⟨Or.inl, fun h => h.elim id (fun both => (no_boundary x both.1).elim)⟩
  let G := F.collapsedCutGraph inclusion q fibers
  let Q := C.cutDiskBoundaryQuotient inclusion disk
  have boundary := C.cutDiskBoundaryQuotient_boundary inclusion disk
    (F.bankBoundary_iff_disk_norm_eq_one retain disk)
  have carrier : G.carrier = Q.boundaryImage := by
    rw [F.collapsedCutGraph_carrier]
    change id '' (C.forgetCuts inclusion '' C.bankBoundary retain) = Q.boundaryImage
    rw [Set.image_id]
    exact (C.cutDiskBoundaryQuotient_boundaryImage inclusion disk).symm
  have contractible : ContractibleSpace G.carrier := by
    rw [carrier]
    exact Q.ball_boundaryImage_contractible_of_sphere P.sphereHomeomorph boundary
  let := contractible
  have adjacency := G.adjacencyGraph_tree_of_contractible
  have connected : G.graph.Connected := by
    obtain ⟨v⟩ := adjacency.connected.nonempty
    exact ⟨⟨v, Set.mem_univ _⟩, fun u _ v _ =>
      G.graph_reaches_iff_adjacency.mpr (adjacency.connected.preconnected u v)⟩
  have mapped_tree : ((C.relativeCutGraph retain Set.univ).map
      (fun v => q (C.vertexPoint Set.univ v))).IsTree := by
    rw [← F.collapsedCutGraph_map_vertex inclusion q fibers]
    exact ⟨connected.mapVertices, G.graph_acyclic_of_contractible.mapVertices Subtype.val_injective⟩
  have original_connected : (C.relativeCutGraph retain Set.univ).Connected :=
    mapped_tree.connected.of_mapVertices (C.vertexPoint_injective Set.univ)
  have original_forest : (C.relativeCutGraph retain Set.univ).IsAcyclic :=
    mapped_tree.isAcyclic.of_mapAlong (G := C.relativeCutGraph retain Set.univ)
      (H := (C.relativeCutGraph retain Set.univ).map (fun v => q (C.vertexPoint Set.univ v)))
      (fun v => q (C.vertexPoint Set.univ v)) id
      (fun _ member => Set.mem_image_of_mem _ member)
      (fun {_ _ _} link => link.map _) Function.injective_id
  let forward (s : C.CutSeam retain) : C.RelativeCutSeam retain Set.univ :=
    ⟨s.val, Set.mem_univ _, s.property⟩
  let backward (s : C.RelativeCutSeam retain Set.univ) : C.CutSeam retain :=
    ⟨s.val, s.property.2⟩
  have to_original (v : C.Vertex Set.univ) (member : v ∈ (C.cutSeamGraph retain).vertexSet) :
      v ∈ (C.relativeCutGraph retain Set.univ).vertexSet := by
    obtain ⟨s, b, equal⟩ := member
    exact Or.inr ⟨forward s, b, equal⟩
  have to_cut (v : C.Vertex Set.univ)
      (member : v ∈ (C.relativeCutGraph retain Set.univ).vertexSet) :
      v ∈ (C.cutSeamGraph retain).vertexSet := by
    rcases member with root | ⟨s, b, equal⟩
    · exact (no_root v root).elim
    · exact ⟨backward s, b, equal⟩
  have forest : (C.cutSeamGraph retain).IsAcyclic :=
    original_forest.of_mapAlong (G := C.cutSeamGraph retain)
      (H := C.relativeCutGraph retain Set.univ) id forward to_original
      (fun {_ _ _} link => link) (by
        intro s t equal
        exact Subtype.ext (congrArg
          (fun z : C.RelativeCutSeam retain Set.univ => z.val) equal))
  have connected : (C.cutSeamGraph retain).Connected := by
    obtain ⟨v, member⟩ := original_connected.1
    refine ⟨⟨v, to_cut v member⟩, ?_⟩
    intro u hu v hv
    obtain ⟨edges, walk⟩ := original_connected.reaches (to_original u hu) (to_original v hv)
    exact ⟨edges.map backward, walk.mapAlong (H := C.cutSeamGraph retain) id backward to_cut
      (fun {_ _ _} link => link)⟩
  exact ⟨connected, forest⟩

theorem cutDisk_iff_cutSeamGraph_tree (retain : Set C.Seam) :
    Nonempty (C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) ↔
      (C.cutSeamGraph retain).IsTree := by
  constructor
  · rintro ⟨disk⟩
    exact P.cutSeamGraph_tree_of_disk retain disk
  · intro tree
    exact P.exists_cutDisk_of_tree retain tree.isAcyclic tree.connected

end Unfoldings.SpatialFolding.ConvexBoundary
