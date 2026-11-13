module

public import Unfoldings.Roof.DevelopmentCoordinates
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Development.BoundaryRays
public import Unfoldings.Complex.ParentBankEndpoints

/-! Actual projected germ vectors and their rigid developed images on parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

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

end Unfoldings.ConvexRoof

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexRoof C)

@[simp] theorem roofDirection_neg (f : Face) (direction : Plane) :
    D.roofDirection K f (-direction) = -D.roofDirection K f direction := by
  simp only [roofDirection, map_neg]

/-- The actual developed boundary ray is the developed image of its projected raw germ. -/
theorem roofDirection_boundaryRay (p : C.BoundaryEnd retain) :
    D.roofDirection K p.val.1.1 (K.projectedGermVector p.val) = D.boundaryRay p := by
  rw [ConvexRoof.projectedGermVector, D.roofDirection_chord, D.boundaryRay_eq_raw]
  rfl

end Unfoldings.FacewiseDevelopment
