module

public import Unfoldings.Complex.BoundaryOrdering
public import Unfoldings.Boundary.Exact
public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Geometry.EdgeParameters
public import Unfoldings.Topology.FiniteEmbeddedGraph

/-!
# The actual bank boundary is a finite embedded multigraph

Boundary vertex copies are the vertices and unpaired banks are the edges.
The edge maps are the original affine edge parametrizations, followed by the
actual metric face maps. Exactness separates all open edges; loops and parallel
edges remain allowed for abstract complexes.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

abbrev BoundaryVertex := {v : C.Vertex retain // C.IsBoundaryVertex retain v}

def bankParameter (bank : C.BoundaryBank retain) (t : unitInterval) :
    (C.triangle bank.val.face).Edge bank.val.edge :=
  ⟨AffineMap.lineMap ((C.triangle bank.val.face).vertex bank.val.edge)
    ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge)) t.val,
    lineMap_mem_segment ℝ _ _ t.property⟩

theorem continuous_bankParameter (bank : C.BoundaryBank retain) :
    Continuous (C.bankParameter retain bank) := by
  unfold bankParameter
  fun_prop

theorem bankParameter_nonvertex (bank : C.BoundaryBank retain) (t : unitInterval)
    (positive : 0 < t) (small : t < 1) :
    ¬ (C.triangle bank.val.face).IsVertex (C.bankParameter retain bank t).val := by
  apply (C.triangle bank.val.face).lineMap_edge_not_vertex bank.val.edge
  exact ⟨positive, small⟩

theorem bankParameter_surjective (bank : C.BoundaryBank retain) :
    Function.Surjective (C.bankParameter retain bank) := by
  intro x
  have member := x.property
  change x.val ∈ segment ℝ ((C.triangle bank.val.face).vertex bank.val.edge)
    ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge)) at member
  rw [segment_eq_image_lineMap] at member
  obtain ⟨t, ht, equal⟩ := member
  exact ⟨⟨t, ht⟩, Subtype.ext equal⟩

theorem bankParameter_injective (bank : C.BoundaryBank retain) :
    Function.Injective (C.bankParameter retain bank) := by
  intro s t same
  have points := congrArg Subtype.val same
  have times := (AffineMap.lineMap_injective ℝ
    ((C.triangle bank.val.face).edge_endpoints_ne bank.val.edge)) points
  exact Subtype.ext times

def boundaryGraph : FiniteEmbeddedGraph (C.BoundaryVertex retain) (C.BoundaryBank retain)
    (C.Realization retain) where
  finite_vertices := inferInstance
  finite_edges := C.finite_boundaryBank retain
  vertex v := C.vertexPoint retain v.val
  vertex_injective := fun _ _ equal => Subtype.ext (C.vertexPoint_injective retain equal)
  left bank := ⟨C.vertexOfCorner retain (bank.val.face, bank.val.edge),
    C.bank_start_isBoundaryVertex retain bank⟩
  right bank := ⟨C.vertexOfCorner retain (bank.val.face, Triangle.next bank.val.edge),
    C.bank_finish_isBoundaryVertex retain bank⟩
  edge bank := ⟨C.bankMap retain bank ∘ C.bankParameter retain bank,
    (C.bankMap_lipschitz retain bank).continuous.comp (C.continuous_bankParameter retain bank)⟩
  edge_zero bank := by
    rw [C.vertexPoint_vertexOfCorner]
    change C.faceMap retain bank.val.face _ = C.faceMap retain bank.val.face _
    apply congrArg
    apply Subtype.ext
    exact AffineMap.lineMap_apply_zero _ _
  edge_one bank := by
    rw [C.vertexPoint_vertexOfCorner]
    change C.faceMap retain bank.val.face _ = C.faceMap retain bank.val.face _
    apply congrArg
    apply Subtype.ext
    exact AffineMap.lineMap_apply_one _ _
  edge_injective bank := by
    intro s hs t _ht equal
    have regular := C.bankParameter_nonvertex retain bank s hs.1 hs.2
    have tagged := (C.bankMap_eq_iff retain bank (C.bankParameter retain bank s) regular
      (C.edgePoint bank (C.bankParameter retain bank t))).mp equal
    have points := congrArg (fun a : C.Total => a.2.val) tagged
    have times := (AffineMap.lineMap_injective ℝ
      ((C.triangle bank.val.face).edge_endpoints_ne bank.val.edge)) points
    exact Subtype.ext times
  edge_avoids_vertices bank t positive small vertex := by
    intro equal
    have regular := C.bankParameter_nonvertex retain bank t positive small
    apply regular
    exact (C.mem_range_vertexPoint_iff retain _).mp ⟨vertex.val, equal.symm⟩
  disjoint_open_edges bank other different := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ ⟨t, _ht, equal⟩
    exact C.bankMap_ne_of_ne retain different (C.bankParameter retain bank s)
      (C.bankParameter retain other t)
      (C.bankParameter_nonvertex retain bank s hs.1 hs.2) equal.symm

theorem vertexPoint_mem_bankBoundary (v : C.BoundaryVertex retain) :
    C.vertexPoint retain v.val ∈ C.bankBoundary retain := by
  obtain ⟨edge, boundary, first | last⟩ := v.property
  · rw [first, C.vertexPoint_vertexOfCorner]
    exact C.bankMap_mem_bankBoundary retain ⟨edge, boundary⟩
      ((C.triangle edge.face).endpoint edge.edge false)
  · rw [last, C.vertexPoint_vertexOfCorner]
    exact C.bankMap_mem_bankBoundary retain ⟨edge, boundary⟩
      ((C.triangle edge.face).endpoint edge.edge true)

theorem boundaryGraph_carrier : (C.boundaryGraph retain).carrier = C.bankBoundary retain := by
  ext p
  constructor
  · intro member
    obtain ⟨index, inside⟩ := Set.mem_iUnion.mp member
    cases index with
    | inl vertex =>
      change p ∈ {C.vertexPoint retain vertex.val} at inside
      rw [Set.mem_singleton_iff] at inside
      rw [inside]
      exact C.vertexPoint_mem_bankBoundary retain vertex
    | inr bank =>
      obtain ⟨t, rfl⟩ := inside
      exact C.bankMap_mem_bankBoundary retain bank (C.bankParameter retain bank t)
  · intro member
    obtain ⟨bank, x, rfl⟩ := Set.mem_iUnion.mp member
    obtain ⟨t, rfl⟩ := C.bankParameter_surjective retain bank x
    exact (C.boundaryGraph retain).mem_carrier_edge bank t

def boundaryEndAsVertex (p : C.BoundaryEnd retain) : C.BoundaryVertex retain :=
  ⟨C.boundaryEndVertex retain p, by
    apply (C.isBoundaryVertex_iff_linkMate_fixed retain _).mpr
    refine ⟨⟨p.val, rfl⟩, ?_⟩
    exact Subtype.ext ((C.mateGerm_eq_self_iff retain p.val).mpr p.property)⟩

theorem boundaryEndAsVertex_mate (p : C.BoundaryEnd retain) :
    C.boundaryEndAsVertex retain (C.boundaryMate retain p) = C.boundaryEndAsVertex retain p :=
  Subtype.ext (C.boundaryMate_spec retain p).2

theorem boundaryGraph_bank_link (p : C.BoundaryEnd retain) :
    (C.boundaryGraph retain).graph.IsLink (C.boundaryEndEquiv retain p).1
      (C.boundaryEndAsVertex retain p)
      (C.boundaryEndAsVertex retain (C.boundaryTurn retain p)) := by
  obtain ⟨⟨bank, side⟩, rfl⟩ := (C.boundaryEndEquiv retain).symm.surjective p
  simp only [boundaryTurn, Equiv.apply_symm_apply]
  cases side
  · left
    constructor <;> apply Subtype.ext <;> rfl
  · right
    constructor <;> apply Subtype.ext <;> rfl

end Unfoldings.TriangleComplex
