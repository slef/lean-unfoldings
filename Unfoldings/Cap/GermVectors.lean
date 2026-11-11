module

public import Unfoldings.Cap.FaceDirections
public import Unfoldings.Cap.VertexProgress
public import Unfoldings.Development.BoundaryRays
public import Unfoldings.Complex.ParentBankEndpoints

/-! Actual projected germ vectors and their rigid developed images on parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def projectedGermVector (p : C.Germ) : Plane :=
  K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2) -
    K.projectFace p.1.1 ((C.triangle p.1.1).vertex p.1.2)

/-- The raw projected vector joins the actual original classes of its boundary endpoints. -/
theorem projectedGermVector_eq_vertices {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    K.projectedGermVector p.val =
      K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain (C.boundaryTurn retain p))) -
      K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex retain p)) := by
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    C.boundaryTurn_corner]
  rfl

/-- The original spatial chord uses the same two actual original endpoint classes. -/
theorem spatialDirection_germVector_eq_vertices {retain : Set C.Seam}
    (p : C.BoundaryEnd retain) :
    K.spatialDirection p.val.1.1 (K.projectedGermVector p.val) =
      K.folding.toSpace Set.univ (C.vertexPoint Set.univ
        (C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex retain (C.boundaryTurn retain p)))) -
      K.folding.toSpace Set.univ (C.vertexPoint Set.univ
        (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p))) := by
  rw [projectedGermVector, K.spatialDirection_chord]
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    C.boundaryTurn_corner]
  rfl

@[simp] theorem spatialDirection_neg (f : Face) (direction : Plane) :
    K.spatialDirection f (-direction) = -K.spatialDirection f direction := by
  simp only [spatialDirection, pullbackDirection, map_neg]

/-- Entrance runs toward the child, opposite to its outward parent vector. -/
theorem projectedGermVector_parent_entrance
    {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
    (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side)
    (outside : ¬ P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p)) e) :
    K.projectedGermVector p.val = -(K.projectedVertex (P.parent e) - K.projectedVertex e) := by
  obtain ⟨first, last⟩ := C.selected_parent_bank_enters S e nonroot p side named outside
  rw [K.projectedGermVector_eq_vertices, first, last]
  exact (neg_sub _ _).symm

/-- Exit follows the outward parent vector with its actual endpoint order. -/
theorem projectedGermVector_parent_exit
    {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
    (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (p : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side)
    (inside : P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p)) e) :
    K.projectedGermVector p.val = K.projectedVertex (P.parent e) - K.projectedVertex e := by
  obtain ⟨first, last⟩ := C.selected_parent_bank_leaves S e nonroot p side named inside
  rw [K.projectedGermVector_eq_vertices, first, last]

/-- Both actual parent-bank faces give the same spatial outward edge vector. -/
theorem spatialDirection_parent_banks
    {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
    (e : C.Vertex Set.univ) (nonroot : e ∉ P.roots)
    (p q : C.BoundaryEnd (C.selectedRetain S)) (side : Bool)
    (first_named : (C.boundaryEndEquiv (C.selectedRetain S) p).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) side)
    (last_named : (C.boundaryEndEquiv (C.selectedRetain S) q).1 =
      C.relativeCutBank (C.selectedRetain S) Set.univ (C.selectedParentCut S e nonroot) (!side))
    (outside : ¬ P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) p)) e)
    (inside : P.Ancestor (C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex (C.selectedRetain S) q)) e) :
    K.spatialDirection p.val.1.1 (K.projectedVertex (P.parent e) - K.projectedVertex e) =
      K.spatialDirection q.val.1.1 (K.projectedVertex (P.parent e) - K.projectedVertex e) := by
  obtain ⟨p_start, p_finish⟩ :=
    C.selected_parent_bank_enters S e nonroot p side first_named outside
  obtain ⟨q_start, q_finish⟩ :=
    C.selected_parent_bank_leaves S e nonroot q (!side) last_named inside
  have first := K.spatialDirection_germVector_eq_vertices p
  have last := K.spatialDirection_germVector_eq_vertices q
  rw [K.projectedGermVector_parent_entrance S e nonroot p side first_named outside,
    K.spatialDirection_neg, p_start, p_finish] at first
  rw [K.projectedGermVector_parent_exit S e nonroot q (!side) last_named inside,
    q_start, q_finish] at last
  apply neg_injective
  rw [first, last, neg_sub]

end Unfoldings.ConvexCap

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

@[simp] theorem developedDirection_neg (f : Face) (direction : Plane) :
    D.developedDirection K f (-direction) = -D.developedDirection K f direction := by
  simp only [developedDirection, ConvexCap.pullbackDirection, map_neg]

/-- The actual developed boundary ray is the developed image of its projected raw germ. -/
theorem developedDirection_boundaryRay (p : C.BoundaryEnd retain) :
    D.developedDirection K p.val.1.1 (K.projectedGermVector p.val) = D.boundaryRay p := by
  rw [ConvexCap.projectedGermVector, D.developedDirection_chord, D.boundaryRay_eq_raw]
  rfl

end Unfoldings.FacewiseDevelopment
