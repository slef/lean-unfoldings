module

public import Unfoldings.Complex.ProcessedParentCuts

/-! Every intermediate ancestor-closed original cut is a rooted forest and cuts a disk to a disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (frontier : P.ParentFrontier)

/-- The original selected edge labels are unchanged at every intermediate stage. -/
theorem processedCut_to_selection_link
    {s : C.RelativeCutSeam (C.processedParentRetain S frontier) Set.univ}
    {a b : C.Vertex Set.univ}
    (link : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsLink s a b) :
    S.graph.IsLink s.val a b := by
  obtain ⟨e, _member, named⟩ :=
    (C.not_mem_processedParentRetain_iff S frontier s.val).mp s.property.2
  apply S.graph_isLink_iff.mpr
  exact ⟨⟨e, named⟩, link⟩

/-- Acyclicity follows from the actual selected forest, preserving all original seam names. -/
theorem processedCut_acyclic :
    (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsAcyclic :=
  S.graph_acyclic.of_mapAlong (fun v => v) Subtype.val (fun _ _ => Set.mem_univ _)
    (fun {_ _ _} link => C.processedCut_to_selection_link S frontier link) Subtype.val_injective

/-- Both ends of every currently cut original edge have already been processed. -/
theorem processedCut_endpoints_processed
    (s : C.RelativeCutSeam (C.processedParentRetain S frontier) Set.univ)
    {a b : C.Vertex Set.univ}
    (link : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsLink s a b) :
    a ∈ frontier.processed ∧ b ∈ frontier.processed := by
  obtain ⟨e, member, named⟩ :=
    (C.not_mem_processedParentRetain_iff S frontier s.val).mp s.property.2
  have original := S.link e
  rw [named] at original
  change C.seamGraph.IsLink s.val a b at link
  rcases link.eq_and_eq_or_eq_and_eq original with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨member, frontier.closed e.val member⟩
  · exact ⟨frontier.closed e.val member, member⟩

variable (roots : P.roots = C.relativeCutRoots Set.univ)

include roots in
/-- The actual intermediate relative graph contains precisely the processed vertices,
including isolated original boundary roots. -/
theorem processedCut_vertex_mem_iff (v : C.Vertex Set.univ) :
    v ∈ (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).vertexSet ↔
      v ∈ frontier.processed := by
  constructor
  · rintro (root | ⟨s, b, rfl⟩)
    · exact frontier.roots (roots.symm ▸ root)
    · have pair := C.processedCut_endpoints_processed S frontier s
        (show (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsLink s
          (C.relativeCutVertex _ _ s false) (C.relativeCutVertex _ _ s true) from Or.inl ⟨rfl, rfl⟩)
      cases b
      · exact pair.1
      · exact pair.2
  · intro member
    by_cases root : v ∈ P.roots
    · exact Or.inl (roots ▸ root)
    · let e : {v : C.Vertex Set.univ // v ∉ P.roots} := ⟨v, root⟩
      let s : C.RelativeCutSeam (C.processedParentRetain S frontier) Set.univ :=
        ⟨S.edge e, Set.mem_univ _,
          (C.not_mem_processedParentRetain_iff S frontier _).mpr ⟨e, member, rfl⟩⟩
      have link : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsLink s
          v (P.parent v) := S.link e
      exact link.left_mem

include roots in
/-- The entire original parent path of a processed vertex is present in the actual cut graph. -/
theorem processedCut_reaches_iterate (v : C.Vertex Set.univ) (member : v ∈ frontier.processed)
    (k : ℕ) : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).Reaches v
      (P.parent^[k] v) := by
  induction k with
  | zero => exact Graph.Reaches.refl ((C.processedCut_vertex_mem_iff S frontier roots v).mpr member)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases root : P.parent^[k] v ∈ P.roots
    · rwa [P.fixed_root _ root]
    · have current := frontier.iterate_mem_of_mem member k
      let e : {v : C.Vertex Set.univ // v ∉ P.roots} := ⟨P.parent^[k] v, root⟩
      let s : C.RelativeCutSeam (C.processedParentRetain S frontier) Set.univ :=
        ⟨S.edge e, Set.mem_univ _,
          (C.not_mem_processedParentRetain_iff S frontier _).mpr ⟨e, current, rfl⟩⟩
      have link : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsLink s
          (P.parent^[k] v) (P.parent (P.parent^[k] v)) := S.link e
      exact ih.trans (Graph.Reaches.of_isLink link)

/-- Every intermediate actual cut route maps into the original selected forest. -/
theorem processedCut_reaches_selection {a b : C.Vertex Set.univ}
    (reach : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).Reaches a b) :
    S.graph.Reaches a b := by
  obtain ⟨edges, walk⟩ := reach
  exact ⟨edges.map Subtype.val, walk.mapAlong (fun v => v) Subtype.val
    (fun _ _ => Set.mem_univ _)
    (fun {_ _ _} link => C.processedCut_to_selection_link S frontier link)⟩

include roots in
/-- Every intermediate original cut forest has exactly one original boundary root per component. -/
theorem processedCut_rootedForest :
    (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).IsRootedForest
      (C.relativeCutRoots Set.univ) := by
  refine ⟨C.processedCut_acyclic S frontier, fun v member => ?_⟩
  have processed := (C.processedCut_vertex_mem_iff S frontier roots v).mp member
  have reach : (C.relativeCutGraph (C.processedParentRetain S frontier) Set.univ).Reaches v
      (P.root v) := by
    simpa only [P.iterate_distanceToRoot_eq_root] using
      C.processedCut_reaches_iterate S frontier roots v processed (P.distanceToRoot v)
  refine ⟨P.root v, ⟨roots ▸ P.root_mem v, reach⟩, ?_⟩
  intro q condition
  obtain ⟨r, _present, unique⟩ := S.graph_rootedForest.2 v (Set.mem_univ _)
  have first := unique (P.root v)
    ⟨P.root_mem v, C.processedCut_reaches_selection S frontier reach⟩
  have last := unique q
    ⟨roots.symm ▸ condition.1, C.processedCut_reaches_selection S frontier condition.2⟩
  exact last.trans first.symm

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ) (frontier : P.ParentFrontier)

include F roots in
/-- Every intermediate first-contact cut of an actual disk is an actual intrinsic cut disk. -/
theorem exists_processed_parent_cutDisk (original : C.Realization Set.univ ≃ₜ
    Metric.closedBall (0 : Plane) 1) :
    Nonempty (C.Realization (C.processedParentRetain S frontier) ≃ₜ
      Metric.closedBall (0 : Plane) 1) :=
  F.exists_cutDisk_of_rootedForest (Set.subset_univ _) original
    (C.processedCut_rootedForest S frontier roots)

end Unfoldings.SpatialFolding
