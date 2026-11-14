module

public import Unfoldings.Polyhedron.UpperCover
public import Unfoldings.Complex.FaceRestriction
public import Unfoldings.Complex.ProjectedEmbedding
public import Unfoldings.Roof.Basic

/-! The actual original upward faces and inherited seams form the full upper convex roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.SupportingNormals

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (N : F.SupportingNormals)

local instance : Fintype N.UpperFace := by classical infer_instance

def upperComplex : TriangleComplex.{u, v} N.UpperFace :=
  C.restrictFaces {f | 0 < N.normal f 2}

def upperFolding : SpatialFolding N.upperComplex where
  place f := F.place f.val
  joined s x := F.joined s.val x

theorem upper_affineTriangles_eq :
    N.upperComplex.affineProjectedTriangle N.projectFaceEquiv = N.upperTriangle := by
  funext f
  apply Triangle.eq_of_vertex_eq
  intro i
  rfl

/-- Every original whole-edge pairing survives with exactly the upward face labels. -/
theorem upper_complete (P : F.ConvexBoundary) :
    ∀ f g : N.UpperFace, f ≠ g → ∀ e d : Fin 3,
      (N.upperTriangle f).edge e = (N.upperTriangle g).edge d →
        ∃ s : N.upperComplex.Seam,
          (N.upperComplex.left s = ⟨f, e⟩ ∧ N.upperComplex.right s = ⟨g, d⟩) ∨
            (N.upperComplex.left s = ⟨g, d⟩ ∧ N.upperComplex.right s = ⟨f, e⟩) := by
  have lift (s : C.Seam) (f g : N.UpperFace) (e d : Fin 3)
      (left : C.left s = ⟨f.val, e⟩) (right : C.right s = ⟨g.val, d⟩) :
      ∃ t : N.upperComplex.Seam,
        N.upperComplex.left t = ⟨f, e⟩ ∧ N.upperComplex.right t = ⟨g, d⟩ := by
    have first : 0 < N.normal (C.left s).face 2 := by rw [left]; exact f.property
    have last : 0 < N.normal (C.right s).face 2 := by rw [right]; exact g.property
    let t : N.upperComplex.Seam := ⟨s, first, last⟩
    refine ⟨t, ?_, ?_⟩
    · apply congrArg₂ EdgeRef.mk
      · exact Subtype.ext (congrArg EdgeRef.face left)
      · exact congrArg EdgeRef.edge left
    · apply congrArg₂ EdgeRef.mk
      · exact Subtype.ext (congrArg EdgeRef.face right)
      · exact congrArg EdgeRef.edge right
  intro f g different e d same
  obtain ⟨s, ⟨left, right⟩ | ⟨left, right⟩⟩ := N.upper_exists_seam P f g different e d same
  · obtain ⟨t, first, last⟩ := lift s f g e d left right
    exact ⟨t, Or.inl ⟨first, last⟩⟩
  · obtain ⟨t, first, last⟩ := lift s g f d e left right
    exact ⟨t, Or.inr ⟨first, last⟩⟩

/-- Closed vertex stars also have exactly one projected intrinsic point. No projection
injectivity or star-connectivity certificate is supplied to this theorem. -/
theorem upper_projection_injective (P : F.ConvexBoundary) :
    Function.Injective (fun x : N.upperComplex.Realization Set.univ =>
      Cap.horizontal (N.upperFolding.toSpace Set.univ x)) := by
  let D := N.upperComplex
  let A := N.projectFaceEquiv
  have triangles := N.upper_affineTriangles_eq
  have joined : ∀ s x, A (D.left s).face x.val = A (D.right s).face (D.identify s x).val :=
    fun s x => congrArg Cap.horizontal (F.joined s.val x)
  have convex : Convex ℝ (⋃ f, (D.affineProjectedTriangle A f).carrier) := by
    rw [triangles, P.upperTriangles_cover_bodyFootprint N]
    exact P.convex_bodyFootprint
  have conforming : TriangleFamily.Conforming (D.affineProjectedTriangle A) :=
    triangles.symm ▸ N.upperTriangles_conforming P
  have separated : Pairwise (fun f g =>
      Disjoint (interior (D.affineProjectedTriangle A f).carrier)
        (interior (D.affineProjectedTriangle A g).carrier)) :=
    triangles.symm ▸ N.upperTriangles_nonoverlapping P
  have complete : ∀ f g : N.UpperFace, f ≠ g → ∀ e d : Fin 3,
      (D.affineProjectedTriangle A f).edge e = (D.affineProjectedTriangle A g).edge d →
        ∃ s : D.Seam, (D.left s = ⟨f, e⟩ ∧ D.right s = ⟨g, d⟩) ∨
          (D.left s = ⟨g, d⟩ ∧ D.right s = ⟨f, e⟩) := by
    rw [triangles]
    exact N.upper_complete P
  intro x y same
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue Set.univ) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue Set.univ) y
  exact (D.point_eq_iff Set.univ a b).mpr
    (D.related_of_affine_projection_eq A joined convex conforming separated complete a b same)

end Unfoldings.SpatialFolding.SupportingNormals

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

local instance : Fintype N.UpperFace := by classical infer_instance

include P in
theorem upperFolding_footprint : Cap.horizontal '' N.upperFolding.surface = P.bodyFootprint := by
  rw [← P.upperTriangles_cover_bodyFootprint N]
  simp only [SpatialFolding.surface, SpatialFolding.faceImage, Set.image_iUnion,
    SupportingNormals.upperTriangle, Triangle.affineImage_carrier, Set.image_image]
  rfl

/-- Construct the full upper roof from the original input geometry alone. Vertical and
lower faces are discarded; all original upward triangles and their seams are preserved. -/
def upperRoof : ConvexRoof N.upperComplex where
  folding := N.upperFolding
  normal f := N.normal f.val
  normal_unit f := N.unit f.val
  normal_upward f := f.property
  normal_tangent f := N.tangent f.val
  supporting f g x :=
    N.supporting f.val _ (F.faceImage_subset_vertexHull g.val ⟨x.val, x.property, rfl⟩)
  projection_injective := N.upper_projection_injective P
  convex_projection := by
    rw [P.upperFolding_footprint N]
    exact P.convex_bodyFootprint
  interior_projection := by
    rw [P.upperFolding_footprint N]
    exact P.interior_bodyFootprint

end Unfoldings.SpatialFolding.ConvexBoundary
