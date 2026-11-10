module

public import Unfoldings.Cap.Basic
public import Unfoldings.Geometry.TriangleAffine
public import Unfoldings.Complex.SubdivisionInteriors

/-!
# The actual projected cap triangulation

Each face projects by an invertible affine map. The resulting closed triangles
cover the footprint and have disjoint interiors. Projected lengths are not
assumed to agree with spatial lengths.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def projectFace (f : Face) : Plane →ᵃ[ℝ] Plane :=
  Cap.horizontal.toAffineMap.comp (K.folding.place f).toAffineMap

@[simp] theorem projectFace_apply (f : Face) (x : Plane) :
    K.projectFace f x = Cap.horizontal (K.folding.place f x) := rfl

theorem projectFace_injective (f : Face) : Function.Injective (K.projectFace f) := by
  intro x y equal
  have bound := K.face_projection_lower f x y
  change K.projectFace f x = K.projectFace f y at equal
  change K.normal f 2 * dist x y ≤ dist (K.projectFace f x) (K.projectFace f y) at bound
  rw [equal, dist_self] at bound
  by_contra different
  exact (not_lt_of_ge bound) (mul_pos (K.normal_upward f) (dist_pos.mpr different))

theorem projectFace_surjective (f : Face) : Function.Surjective (K.projectFace f) :=
  (K.projectFace f).linear_surjective_iff.mp
    (LinearMap.surjective_of_injective
      ((K.projectFace f).linear_injective_iff.mpr (K.projectFace_injective f)))

def projectFaceEquiv (f : Face) : Plane ≃ᵃ[ℝ] Plane :=
  AffineEquiv.ofBijective (φ := K.projectFace f)
    ⟨K.projectFace_injective f, K.projectFace_surjective f⟩

def projectFaceHomeomorph (f : Face) : Plane ≃ₜ Plane :=
  { (K.projectFaceEquiv f).toEquiv with
    continuous_toFun := (K.projectFace f).continuous_of_finiteDimensional
    continuous_invFun := (K.projectFaceEquiv f).symm.toAffineMap.continuous_of_finiteDimensional }

def projectedTriangle (f : Face) : Triangle :=
  (C.triangle f).affineImage (K.projectFace f) (K.projectFace_injective f)

@[simp] theorem projectedTriangle_vertex (f : Face) (i : Fin 3) :
    (K.projectedTriangle f).vertex i =
      Cap.horizontal (K.folding.place f ((C.triangle f).vertex i)) :=
  rfl

theorem projectedTriangle_carrier (f : Face) :
    (K.projectedTriangle f).carrier = Cap.horizontal '' K.folding.faceImage f := by
  rw [projectedTriangle, Triangle.affineImage_carrier, SpatialFolding.faceImage, Set.image_image]
  rfl

theorem footprint_eq_union_projectedTriangles :
    K.footprint = ⋃ f, (K.projectedTriangle f).carrier := by
  simp only [footprint, SpatialFolding.surface, Set.image_iUnion, K.projectedTriangle_carrier]

theorem projectedTriangles_nonoverlapping {f g : Face} (different : f ≠ g) :
    Disjoint (interior (K.projectedTriangle f).carrier)
      (interior (K.projectedTriangle g).carrier) := by
  have carrier (f : Face) : (K.projectedTriangle f).carrier =
      K.projectFaceHomeomorph f '' (C.triangle f).carrier :=
    (C.triangle f).affineImage_carrier _ _
  rw [carrier f, carrier g, ← Homeomorph.image_interior, ← Homeomorph.image_interior]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, first⟩ ⟨y, hy, last⟩
  let a : C.Cell f := ⟨x, interior_subset hx⟩
  let b : C.Cell g := ⟨y, interior_subset hy⟩
  have equal : C.faceMap Set.univ f a = C.faceMap Set.univ g b :=
    K.projection_injective (first.trans last.symm)
  have related := (C.faceMap_eq_iff Set.univ f g a b).mp equal
  have tags : (⟨f, a⟩ : C.Total) = ⟨g, b⟩ := C.eq_of_related_interior hx related
  exact different (congrArg Sigma.fst tags)

theorem projectedTriangle_joined (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    K.projectFace (C.left s).face x.val =
      K.projectFace (C.right s).face (C.identify s x).val :=
  congrArg Cap.horizontal (K.folding.joined s x)

end Unfoldings.ConvexCap
