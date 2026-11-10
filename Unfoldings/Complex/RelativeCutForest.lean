module

public import Unfoldings.Complex.RelativeCutDisk
public import Unfoldings.Complex.CollapsedCutCarrier
public import Unfoldings.Complex.DiskSphereFibers
public import Unfoldings.Topology.GraphRootQuotient

/-!
# The full relative disk forest criterion

Further edge cuts of an actual disk produce one disk if and only if the new
cut seams form a forest with exactly one original-boundary root per component.
Original bank edges are excluded from the cut-edge type. Isolated original
boundary vertices are harmless rooted singleton components, so empty cuts work.
The criterion concerns intrinsic cut topology and permits overlapping layouts.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

include F inclusion

theorem rootedForest_of_cutDisk
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    (cut : C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) :
    (C.relativeCutGraph small large).IsRootedForest (C.relativeCutRoots large) := by
  let q := originalDiskSphereProjection original
  have fibers : ∀ x y, q x = q y ↔
      x = y ∨ (x ∈ C.bankBoundary large ∧ y ∈ C.bankBoundary large) :=
    F.originalDiskSphereProjection_fibers original
  let G := F.collapsedCutGraph inclusion q fibers
  have carrier : G.carrier =
      (F.cutDiskBoundarySphereQuotient inclusion original).boundaryImage := by
    rw [F.collapsedCutGraph_carrier]
    rw [Set.image_image]
    rfl
  have contractible : ContractibleSpace G.carrier := by
    rw [carrier]
    exact F.cutDiskBoundarySphereImage_contractible inclusion original cut
  let := contractible
  have adjacency := G.adjacencyGraph_tree_of_contractible
  have connected : G.graph.Connected := by
    obtain ⟨v⟩ := adjacency.connected.nonempty
    exact ⟨⟨v, Set.mem_univ _⟩, fun u _ v _ =>
      G.graph_reaches_iff_adjacency.mpr (adjacency.connected.preconnected u v)⟩
  have mapped_tree : ((C.relativeCutGraph small large).map
      (fun v => q (C.vertexPoint large v))).IsTree := by
    rw [← F.collapsedCutGraph_map_vertex inclusion q fibers]
    exact ⟨connected.mapVertices, G.graph_acyclic_of_contractible.mapVertices Subtype.val_injective⟩
  have exact_fibers : ∀ u ∈ (C.relativeCutGraph small large).vertexSet,
      ∀ v ∈ (C.relativeCutGraph small large).vertexSet,
      q (C.vertexPoint large u) = q (C.vertexPoint large v) ↔
        u = v ∨ (u ∈ C.relativeCutRoots large ∧ v ∈ C.relativeCutRoots large) := by
    intro u _hu v _hv
    rw [fibers, (C.vertexPoint_injective large).eq_iff,
      C.vertexPoint_mem_bankBoundary_iff, C.vertexPoint_mem_bankBoundary_iff]
    rfl
  obtain ⟨root⟩ := (F.boundaryGraph_connected_of_disk large original).nonempty
  exact (C.relativeCutGraph small large).isRootedForest_of_map_tree
    (C.relativeCutRoots large) (fun v => q (C.vertexPoint large v)) (fun _ h => Or.inl h)
    ⟨root.val, root.property⟩ exact_fibers mapped_tree

theorem cutDisk_iff_rootedForest
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1) :
    Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) ↔
      (C.relativeCutGraph small large).IsRootedForest (C.relativeCutRoots large) := by
  constructor
  · rintro ⟨cut⟩
    exact F.rootedForest_of_cutDisk inclusion original cut
  · exact F.exists_cutDisk_of_rootedForest inclusion original

omit inclusion in
theorem rootedForest_no_new_cuts (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) :
    (C.relativeCutGraph retain retain).IsRootedForest (C.relativeCutRoots retain) :=
  F.rootedForest_of_cutDisk (Set.Subset.rfl) disk disk

theorem not_cutDisk_of_cutCycle
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    {s : C.RelativeCutSeam small large} (cycle : (C.relativeCutGraph small large).LiesOnCycle s) :
    ¬ Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  rintro ⟨cut⟩
  exact (F.rootedForest_of_cutDisk inclusion original cut).1.not_liesOnCycle s cycle

theorem not_cutDisk_of_two_boundary_roots
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    {u v : C.Vertex large} (ur : u ∈ C.relativeCutRoots large)
    (vr : v ∈ C.relativeCutRoots large) (different : u ≠ v)
    (path : (C.relativeCutGraph small large).Reaches u v) :
    ¬ Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  rintro ⟨cut⟩
  obtain ⟨r, _member, unique⟩ :=
    (F.rootedForest_of_cutDisk inclusion original cut).2 u (Or.inl ur)
  exact different ((unique u ⟨ur, Graph.Reaches.refl (Or.inl ur)⟩).trans
    (unique v ⟨vr, path⟩).symm)

theorem not_cutDisk_of_unrooted_component
    (original : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    {v : C.Vertex large} (member : v ∈ (C.relativeCutGraph small large).vertexSet)
    (unrooted : ∀ r ∈ C.relativeCutRoots large, ¬ (C.relativeCutGraph small large).Reaches v r) :
    ¬ Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  rintro ⟨cut⟩
  obtain ⟨r, ⟨root, reach⟩, _unique⟩ :=
    (F.rootedForest_of_cutDisk inclusion original cut).2 v member
  exact unrooted r root reach

end Unfoldings.SpatialFolding
