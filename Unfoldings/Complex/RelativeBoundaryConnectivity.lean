module

public import Unfoldings.Complex.RelativePairedBanks
public import Unfoldings.Complex.BoundaryComponentDescent

/-!
# Rooted forest cuts have connected actual bank boundary

Boundary-component labels descend through the restored original vertex classes.
Old boundary banks keep all root labels equal. The outside extension then
propagates that label to every new bank component.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)
  (forest : (C.relativeCutRootExtension small large).IsAcyclic)

include inclusion forest

theorem relativeComponent_eq_of_crossing {p q : C.Germ}
    (crossing : C.GermCrosses large p q) :
    C.vertexBoundaryComponent small (C.vertexOfCorner small p.1) =
      C.vertexBoundaryComponent small (C.vertexOfCorner small q.1) := by
  obtain ⟨s, retained, side, b, rfl, rfl⟩ := crossing
  by_cases kept : s ∈ small
  · exact congrArg (C.vertexBoundaryComponent small)
      (show C.GermCrosses small
        (C.germOfEndpoint (C.seamSide s side) b)
        (C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side b))
        from ⟨s, kept, side, b, rfl, rfl⟩).vertex_eq
  · exact C.vertexBoundaryComponent_eq_of_reaches small
      (C.relativeBoundaryEnds_reaches inclusion forest ⟨s, retained, kept⟩ side b
        (C.acrossEndpoint s side b))

theorem relativeComponent_eq_of_germStep {p q : C.Germ}
    (step : C.GermStep large p q) :
    C.vertexBoundaryComponent small (C.vertexOfCorner small p.1) =
      C.vertexBoundaryComponent small (C.vertexOfCorner small q.1) := by
  rcases step with rfl | rfl
  · rfl
  · by_cases boundary : C.IsBoundaryEdge large (C.germEdge p)
    · rw [(C.mateGerm_eq_self_iff large p).mpr boundary]
    · obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff large p).mpr boundary
      rw [C.mateGerm_of_crossing crossing]
      exact C.relativeComponent_eq_of_crossing inclusion forest crossing

theorem relativeComponent_eq_of_germs_related {p q : C.Germ}
    (related : Relation.EqvGen (C.GermStep large) p q) :
    C.vertexBoundaryComponent small (C.vertexOfCorner small p.1) =
      C.vertexBoundaryComponent small (C.vertexOfCorner small q.1) := by
  induction related with
  | rel p q step => exact C.relativeComponent_eq_of_germStep inclusion forest step
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def relativeVertexBoundaryComponent (v : C.Vertex large) :
    Option (C.boundaryGraph small).adjacencyGraph.ConnectedComponent :=
  Quotient.lift (fun c => C.vertexBoundaryComponent small (C.vertexOfCorner small c))
    (fun c d related => C.relativeComponent_eq_of_germs_related inclusion forest
      ((C.germs_related_iff_vertex_eq large (c, false) (d, false)).mpr
        ((C.vertexOfCorner_eq_iff large c d).mpr related))) v

@[simp] theorem relativeVertexBoundaryComponent_forget (v : C.Vertex small) :
    C.relativeVertexBoundaryComponent inclusion forest (C.vertexForgetCuts inclusion v) =
      C.vertexBoundaryComponent small v := by
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective small v
  rfl

theorem relativeComponent_cutLink {s : C.RelativeCutSeam small large} {u v : C.Vertex large}
    (link : (C.relativeCutGraph small large).IsLink s u v) :
    C.relativeVertexBoundaryComponent inclusion forest u =
      C.relativeVertexBoundaryComponent inclusion forest v := by
  have canonical :
      C.relativeVertexBoundaryComponent inclusion forest (C.relativeCutVertex small large s false) =
        C.relativeVertexBoundaryComponent inclusion forest
          (C.relativeCutVertex small large s true) := by
    let G := C.boundaryGraph small
    let bank := C.relativeCutBank small large s false
    change C.relativeVertexBoundaryComponent inclusion forest
        (C.vertexForgetCuts inclusion (G.left bank).val) =
      C.relativeVertexBoundaryComponent inclusion forest
        (C.vertexForgetCuts inclusion (G.right bank).val)
    rw [C.relativeVertexBoundaryComponent_forget, C.relativeVertexBoundaryComponent_forget]
    exact C.vertexBoundaryComponent_eq_of_reaches small
      (Graph.Reaches.of_isLink (show G.graph.IsLink bank (G.left bank) (G.right bank)
        from Or.inl ⟨rfl, rfl⟩))
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact canonical
  · exact canonical.symm

theorem relativeComponent_oldBank (bank : C.BoundaryBank large) :
    C.relativeVertexBoundaryComponent inclusion forest ((C.boundaryGraph large).left bank).val =
      C.relativeVertexBoundaryComponent inclusion forest
        ((C.boundaryGraph large).right bank).val := by
  let copy : C.BoundaryBank small :=
    ⟨bank.val, C.isBoundaryEdge_antitone inclusion bank.property⟩
  let G := C.boundaryGraph small
  change C.relativeVertexBoundaryComponent inclusion forest
      (C.vertexForgetCuts inclusion (G.left copy).val) =
    C.relativeVertexBoundaryComponent inclusion forest
      (C.vertexForgetCuts inclusion (G.right copy).val)
  rw [C.relativeVertexBoundaryComponent_forget, C.relativeVertexBoundaryComponent_forget]
  exact C.vertexBoundaryComponent_eq_of_reaches small
    (Graph.Reaches.of_isLink (show G.graph.IsLink copy (G.left copy) (G.right copy)
      from Or.inl ⟨rfl, rfl⟩))

theorem relativeComponent_oldBoundary
    (connected : (C.boundaryGraph large).adjacencyGraph.Connected)
    (u v : C.BoundaryVertex large) :
    C.relativeVertexBoundaryComponent inclusion forest u.val =
      C.relativeVertexBoundaryComponent inclusion forest v.val := by
  obtain ⟨edges, walk⟩ := (C.boundaryGraph large).graph_reaches_iff_adjacency.mpr
    (connected.preconnected u v)
  apply walk.eq_of_link_invariant
    (fun v => C.relativeVertexBoundaryComponent inclusion forest v.val)
  intro bank a b link
  rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact C.relativeComponent_oldBank inclusion forest bank
  · exact (C.relativeComponent_oldBank inclusion forest bank).symm

theorem boundaryGraph_connected_of_relativeCutTree
    (old_connected : (C.boundaryGraph large).adjacencyGraph.Connected)
    (connected : (C.relativeCutRootExtension small large).Connected) :
    (C.boundaryGraph small).adjacencyGraph.Connected := by
  obtain ⟨root⟩ := old_connected.nonempty
  let label : Option (C.Vertex large) →
      Option (C.boundaryGraph small).adjacencyGraph.ConnectedComponent
    | none => C.relativeVertexBoundaryComponent inclusion forest root.val
    | some v => C.relativeVertexBoundaryComponent inclusion forest v
  have step {edge : C.RelativeCutSeam small large ⊕ C.relativeCutRoots large}
      {a b : Option (C.Vertex large)}
      (link : (C.relativeCutRootExtension small large).IsLink edge a b) : label a = label b := by
    cases edge with
    | inl s =>
      obtain ⟨u, v, link, rfl, rfl⟩ := link
      exact C.relativeComponent_cutLink inclusion forest link
    | inr r =>
      have same := C.relativeComponent_oldBoundary inclusion forest old_connected
        (⟨r.val, r.property⟩ : C.BoundaryVertex large) root
      rcases link with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact same.symm
      · exact same
  have reaches (u v : C.BoundaryVertex small) :
      (C.boundaryGraph small).adjacencyGraph.Reachable u v := by
    obtain ⟨edges, walk⟩ := connected.reaches
      (show some (C.relativeBoundaryVertex inclusion u) ∈
          (C.relativeCutRootExtension small large).vertexSet
        from Or.inl (C.relativeBoundaryVertex_member inclusion u))
      (show some (C.relativeBoundaryVertex inclusion v) ∈
          (C.relativeCutRootExtension small large).vertexSet
        from Or.inl (C.relativeBoundaryVertex_member inclusion v))
    have same := walk.eq_of_link_invariant label @step
    change C.relativeVertexBoundaryComponent inclusion forest
        (C.vertexForgetCuts inclusion u.val) =
      C.relativeVertexBoundaryComponent inclusion forest
        (C.vertexForgetCuts inclusion v.val) at same
    rw [C.relativeVertexBoundaryComponent_forget, C.relativeVertexBoundaryComponent_forget,
      C.vertexBoundaryComponent_boundary, C.vertexBoundaryComponent_boundary] at same
    exact SimpleGraph.ConnectedComponent.eq.mp (Option.some_injective _ same)
  have nonempty : Nonempty (C.BoundaryVertex small) := by
    obtain ⟨edge, boundary, _which⟩ := root.property
    exact ⟨(C.boundaryGraph small).left
      ⟨edge, C.isBoundaryEdge_antitone inclusion boundary⟩⟩
  exact { preconnected := reaches, nonempty := nonempty }

end Unfoldings.TriangleComplex
