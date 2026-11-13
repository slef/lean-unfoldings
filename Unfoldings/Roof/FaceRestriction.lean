module

public import Unfoldings.Roof.Basic
public import Unfoldings.Complex.FaceRestrictionClasses

/-! Restricting an embedded roof to whole faces can identify only boundary vertex copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

open Classical in
/-- A whole-face subcomplex inherits the original rigid spatial placements and seam maps. -/
def restrictFaces (U : Set Face) : SpatialFolding (C.restrictFaces U) where
  place f := F.place f.val
  joined s x := F.joined s.val x

end Unfoldings.SpatialFolding

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- The actual planar projection of the intrinsic whole-face restriction. Vertex pinches
are represented by distinct intrinsic points even if their planar images coincide. -/
def restrictProjection (U : Set Face) : C((C.restrictFaces U).Realization Set.univ, Plane) :=
  ⟨fun x => Cap.horizontal ((K.folding.restrictFaces U).toSpace Set.univ x),
    Cap.horizontalCLM.continuous.comp
      ((K.folding.restrictFaces U).toSpace_lipschitz Set.univ).continuous⟩

open Classical in
@[simp] theorem restrictProjection_faceMap (U : Set Face) (f : {f : Face // f ∈ U})
    (x : (C.restrictFaces U).Cell f) :
    K.restrictProjection U ((C.restrictFaces U).faceMap Set.univ f x) =
      Cap.horizontal (K.folding.place f.val x.val) := rfl

open Classical in
/-- Any fiber starting at a nonvertex face point is a singleton, even after deleting faces.
Thus any failure of injectivity of a face restriction consists solely of vertex pinches. -/
theorem restrictProjection_fiber_regular (U : Set Face) (f : {f : Face // f ∈ U})
    (x : (C.restrictFaces U).Cell f) (regular : ¬ (C.triangle f.val).IsVertex x.val)
    (y : (C.restrictFaces U).Realization Set.univ)
    (same : K.restrictProjection U ((C.restrictFaces U).faceMap Set.univ f x) =
      K.restrictProjection U y) :
    (C.restrictFaces U).faceMap Set.univ f x = y := by
  obtain ⟨⟨g, z⟩, rfl⟩ := MetricGluing.point_surjective
    (C.restrictFaces U).Cell ((C.restrictFaces U).glue Set.univ) y
  have raw : C.faceMap Set.univ f.val x = C.faceMap Set.univ g.val z :=
    K.projection_injective same
  have related := (C.faceMap_eq_iff Set.univ f.val g.val x z).mp raw
  have restricted := C.restrict_eqvGen_of_regular U Set.univ
    (a := ⟨f, x⟩) (b := ⟨g, z⟩) regular related
  have retained : C.restrictRetain U Set.univ = Set.univ := by
    ext s
    rfl
  rw [retained] at restricted
  exact ((C.restrictFaces U).faceMap_eq_iff Set.univ f g x z).mpr restricted

end Unfoldings.ConvexRoof
