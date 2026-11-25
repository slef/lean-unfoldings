module

public import Unfoldings.Roof.AffineFloorLineSubdivision
public import Unfoldings.Roof.ConvexRestriction
public import Unfoldings.Development.AffineProjectionEmbedding

/-! A complete parent patch has an embedded affine development in either metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement

universe u

variable {I J : Type u} [Fintype I] [Nonempty I]
  {family : I → SpatialPlane} {floor : Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  {extra : J → Plane →ᵃ[ℝ] ℝ} {T : FloorMesh family floor extra Z}
  {A : Type u} {equation : A → Plane →ᵃ[ℝ] ℝ} (L : T.LineRefinement equation)

local instance patchIndexFintype : Fintype L.mesh.Index := @Fintype.ofFinite _ L.mesh.finite

/-- The closed fine triangles of one original face, with its inherited seams. -/
def parentPieces (f : T.Index) : Set L.mesh.Index := {g | L.parent g = f}

open Classical in
def parentComplex (f : T.Index) := L.mesh.pairedComplex.restrictFaces (L.parentPieces f)

variable (f : T.Index) (A' : Plane ≃ᵃ[ℝ] Plane)

private theorem parent_support (g : L.parentPieces f) : L.mesh.support g.val = T.support f :=
  (L.same_support g.val).trans (congrArg T.support g.property)

open Classical in
theorem parentAffine_joined (s : (L.parentComplex f).Seam)
    (x : ((L.parentComplex f).triangle ((L.parentComplex f).left s).face).Edge
      ((L.parentComplex f).left s).edge) :
    A' x.val = A' ((L.parentComplex f).identify s x).val := by
  apply congrArg A'
  apply (family (T.support f)).place.injective
  have join := L.mesh.pairedFolding.joined s.val x
  change (family (L.mesh.support (L.mesh.pairedComplex.left s.val).face)).place x.val =
    (family (L.mesh.support (L.mesh.pairedComplex.right s.val).face)).place
      ((L.parentComplex f).identify s x).val at join
  have left_eq : L.mesh.support (L.mesh.pairedComplex.left s.val).face = T.support f :=
    L.parent_support f ((L.parentComplex f).left s).face
  have right_eq : L.mesh.support (L.mesh.pairedComplex.right s.val).face = T.support f :=
    L.parent_support f ((L.parentComplex f).right s).face
  rwa [left_eq, right_eq] at join

open Classical in
theorem parentAffine_triangle_carrier (g : L.parentPieces f) :
    ((L.parentComplex f).affineProjectedTriangle (fun _ => A') g).carrier =
      (((family (T.support f)).project.symm.trans A') '' (L.mesh.projectedTriangle g.val).carrier) := by
  calc
    _ = A' '' (L.mesh.triangle g.val).carrier :=
      (L.mesh.triangle g.val).affineImage_carrier A'.toAffineMap A'.injective
    _ = _ := by
      rw [L.mesh.triangle_carrier, L.parent_support f g, Set.image_image]
      rfl

open Classical in
theorem parentAffine_separated : Pairwise (fun g h : L.parentPieces f =>
    Disjoint (interior ((L.parentComplex f).affineProjectedTriangle (fun _ => A') g).carrier)
      (interior ((L.parentComplex f).affineProjectedTriangle (fun _ => A') h).carrier)) := by
  intro g h different
  rw [L.parentAffine_triangle_carrier f A', L.parentAffine_triangle_carrier f A']
  let H := ((family (T.support f)).project.symm.trans A').toContinuousAffineEquiv.toHomeomorph
  change Disjoint (interior (H '' _)) (interior (H '' _))
  rw [← H.image_interior, ← H.image_interior, Set.disjoint_image_iff H.injective]
  exact L.mesh.separated (fun eq => different (Subtype.ext eq))

open Classical in
def parentAffineComplex :=
  (L.parentComplex f).affineProjectionComplex (fun _ => A') (L.parentAffine_joined f A')

open Classical in
def parentAffineDevelopment : FacewiseDevelopment (L.parentAffineComplex f A') Set.univ :=
  (L.parentComplex f).affineProjectionDevelopment (fun _ => A') (L.parentAffine_joined f A')
    (L.parentAffine_separated f A')

open Classical in
theorem parentAffineDevelopment_range :
    Set.range (L.parentAffineDevelopment f A').toPlane =
      ((T.triangle f).affineImage A'.toAffineMap A'.injective).carrier := by
  have h := (L.parentComplex f).affineProjectionDevelopment_range
    (fun _ => A') (L.parentAffine_joined f A') (L.parentAffine_separated f A')
  calc
    _ = ⋃ g : L.parentPieces f,
        ((L.parentComplex f).affineProjectedTriangle (fun _ => A') g).carrier := h
    _ = A' '' (T.triangle f).carrier := by
      simp_rw [L.parentAffine_triangle_carrier f A']
      have cover : (⋃ g : L.parentPieces f, (L.mesh.projectedTriangle g.val).carrier) =
          (T.projectedTriangle f).carrier := (L.projected_parent_cover f).symm
      rw [← Set.image_iUnion, cover, T.triangle_carrier, Set.image_image]
      rfl
    _ = _ := ((T.triangle f).affineImage_carrier A'.toAffineMap A'.injective).symm

open Classical in
theorem parentAffineDevelopment_injective
    (inside : (interior (clipAbove family floor Z)).Nonempty) :
    Function.Injective (L.parentAffineDevelopment f A').toPlane := by
  let R := L.mesh.roof inside
  let U := L.parentPieces f
  have footprint : R.restrictedCarrier U = (T.projectedTriangle f).carrier := by
    change (⋃ g : L.parentPieces f, (R.projectedTriangle g.val).carrier) = _
    calc
      _ = ⋃ g : L.parentPieces f, (L.mesh.projectedTriangle g.val).carrier :=
        Set.iUnion_congr (fun g => congrArg Triangle.carrier (L.mesh.roof_projectedTriangle inside g.val))
      _ = _ := (L.projected_parent_cover f).symm
  have nonempty : U.Nonempty := by
    obtain ⟨g, _⟩ := Set.mem_iUnion.mp ((L.projected_parent_cover f).subset
      ((T.projectedTriangle f).vertex_mem 0))
    exact ⟨g.val, g.property⟩
  have injective := R.restrictProjection_injective_of_convex U nonempty
    (footprint.symm ▸ (T.projectedTriangle f).convex_carrier)
  apply (L.parentComplex f).affineProjectionDevelopment_injective (fun _ => A')
    (L.parentAffine_joined f A') (L.parentAffine_separated f A')
  intro a b equal
  apply ((L.parentComplex f).point_eq_iff Set.univ a b).mp
  apply injective
  change Cap.horizontal ((family (L.mesh.support a.1.val)).place a.2.val) =
    Cap.horizontal ((family (L.mesh.support b.1.val)).place b.2.val)
  rw [L.parent_support f a.1, L.parent_support f b.1, A'.injective equal]

end Unfoldings.SpatialEnvelope.FloorMesh.LineRefinement
