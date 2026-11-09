module

public import Unfoldings.Topology.QuotientRetraction
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Quotients whose identifications occur only on a boundary

A distinguished subset of the domain records the boundary being glued.
Distinct points in a projection fiber must both belong to this subset.
No manifold, disk, or separation conclusion is part of the definition.
The projection identifies the boundary complements homeomorphically when the
boundary is closed. Boundary retractions descend to punctured target spaces.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

structure BoundaryQuotient (A X : Type*) [TopologicalSpace A] [TopologicalSpace X] where
  projection : C(A, X)
  quotient : Topology.IsQuotientMap projection
  boundary : Set A
  fibers : ∀ a b, projection a = projection b →
    a = b ∨ (a ∈ boundary ∧ b ∈ boundary)

namespace BoundaryQuotient

variable {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
  (Q : BoundaryQuotient A X)

def boundaryImage : Set X := Q.projection '' Q.boundary

def precomp {B : Type*} [TopologicalSpace B] (H : B ≃ₜ A) : BoundaryQuotient B X where
  projection := Q.projection.comp ⟨H, H.continuous⟩
  quotient := Q.quotient.comp H.isQuotientMap
  boundary := H ⁻¹' Q.boundary
  fibers := by
    intro a b equal
    rcases Q.fibers (H a) (H b) equal with same | both
    · exact Or.inl (H.injective same)
    · exact Or.inr both

theorem precomp_boundaryImage {B : Type*} [TopologicalSpace B] (H : B ≃ₜ A) :
    (Q.precomp H).boundaryImage = Q.boundaryImage := by
  ext x
  constructor
  · rintro ⟨b, hb, equal⟩
    exact ⟨H b, hb, equal⟩
  · rintro ⟨a, ha, equal⟩
    refine ⟨H.symm a, ?_, ?_⟩
    · change H (H.symm a) ∈ Q.boundary
      simpa only [H.apply_symm_apply] using ha
    · change Q.projection (H (H.symm a)) = x
      simpa only [H.apply_symm_apply] using equal

theorem projection_mem_boundaryImage_iff (a : A) :
    Q.projection a ∈ Q.boundaryImage ↔ a ∈ Q.boundary := by
  constructor
  · rintro ⟨b, hb, equal⟩
    rcases Q.fibers a b equal.symm with same | both
    · exact same ▸ hb
    · exact both.1
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem preimage_boundaryImage : Q.projection ⁻¹' Q.boundaryImage = Q.boundary :=
  Set.ext (Q.projection_mem_boundaryImage_iff)

theorem isClosed_boundaryImage (closed : IsClosed Q.boundary) : IsClosed Q.boundaryImage := by
  rw [← Q.quotient.isCoinducing.isClosed_preimage, Q.preimage_boundaryImage]
  exact closed

def complementHomeomorph (closed : IsClosed Q.boundary) :
    ↥(Q.boundaryᶜ) ≃ₜ ↥(Q.boundaryImageᶜ) := by
  let H : ↥(Q.boundaryᶜ) ≃ₜ ↥(Q.projection ⁻¹' Q.boundaryImageᶜ) :=
    Homeomorph.setCongr (by rw [Set.preimage_compl, Q.preimage_boundaryImage])
  let restricted := Q.boundaryImageᶜ.restrictPreimage Q.projection
  let f := restricted ∘ H
  have quotient : Topology.IsQuotientMap f :=
    (Q.quotient.restrictPreimage_isOpen (Q.isClosed_boundaryImage closed).isOpen_compl).comp
      H.isQuotientMap
  have injective : Function.Injective f := by
    intro a b equal
    have images : Q.projection a.val = Q.projection b.val := congrArg Subtype.val equal
    rcases Q.fibers a.val b.val images with same | both
    · exact Subtype.ext same
    · exact (a.property both.1).elim
  exact (Equiv.ofBijective f ⟨injective, quotient.surjective⟩).toHomeomorph
    (fun _ => quotient.isCoinducing.isOpen_preimage)

@[simp] theorem complementHomeomorph_apply (closed : IsClosed Q.boundary)
    (a : ↥(Q.boundaryᶜ)) : (Q.complementHomeomorph closed a).val = Q.projection a.val := rfl

theorem projection_center_not_mem (center : A) (outside : center ∉ Q.boundary) :
    Q.projection center ∉ Q.boundaryImage :=
  fun member => outside ((Q.projection_mem_boundaryImage_iff center).mp member)

def boundaryImageInclusion (center : A) (outside : center ∉ Q.boundary) :
    C(Q.boundaryImage, ↥(({Q.projection center} : Set X)ᶜ)) := by
  have avoids (x : Q.boundaryImage) : x.val ≠ Q.projection center := by
    intro equal
    exact Q.projection_center_not_mem center outside (equal ▸ x.property)
  exact ⟨fun x => ⟨x.val, avoids x⟩, continuous_subtype_val.subtype_mk avoids⟩

theorem exists_boundary_retraction [T1Space X] (center : A) (outside : center ∉ Q.boundary)
    (retract : C(↥(({center} : Set A)ᶜ), Q.boundary))
    (identity : ∀ b : Q.boundary, ∀ h : b.val ≠ center, retract ⟨b.val, h⟩ = b) :
    ∃ R : C(↥(({Q.projection center} : Set X)ᶜ), Q.boundaryImage),
      ∀ b, R (Q.boundaryImageInclusion center outside b) = b := by
  let puncture : Set X := {Q.projection center}ᶜ
  let fiber := Q.projection ⁻¹' puncture
  let restricted := puncture.restrictPreimage Q.projection
  have avoids (x : fiber) : x.val ≠ center := by
    intro equal
    exact x.property (congrArg Q.projection equal)
  let punctured (x : fiber) : ↥(({center} : Set A)ᶜ) := ⟨x.val, avoids x⟩
  have continuous_punctured : Continuous punctured := continuous_subtype_val.subtype_mk avoids
  let folded (x : fiber) : Q.boundaryImage :=
    ⟨Q.projection (retract (punctured x)), (retract (punctured x)).val,
      (retract (punctured x)).property, rfl⟩
  have continuous_folded : Continuous folded :=
    (Q.projection.continuous.comp
      (continuous_subtype_val.comp (retract.continuous.comp continuous_punctured))).subtype_mk _
  have on_boundary (x : fiber) (member : x.val ∈ Q.boundary) :
      (folded x).val = Q.projection x.val := by
    have same := identity ⟨x.val, member⟩ (avoids x)
    exact congrArg (fun b : Q.boundary => Q.projection b.val) same
  have fibers : ∀ x y : fiber, restricted x = restricted y → folded x = folded y := by
    intro x y equal
    have images : Q.projection x.val = Q.projection y.val := congrArg Subtype.val equal
    rcases Q.fibers x.val y.val images with same | both
    · exact congrArg folded (Subtype.ext same)
    · exact Subtype.ext ((on_boundary x both.1).trans
        (images.trans (on_boundary y both.2).symm))
  have quotient : Topology.IsQuotientMap restricted :=
    Q.quotient.restrictPreimage_isOpen isOpen_compl_singleton
  let R := quotientContinuousDesc restricted quotient ⟨folded, continuous_folded⟩ fibers
  refine ⟨R, ?_⟩
  intro b
  obtain ⟨a, ha, image⟩ := b.property
  have avoids_center : Q.projection a ≠ Q.projection center := by
    rw [image]
    exact (Q.boundaryImageInclusion center outside b).property
  let lift : fiber := ⟨a, avoids_center⟩
  have equal : restricted lift = Q.boundaryImageInclusion center outside b := Subtype.ext image
  rw [← equal]
  change quotientContinuousDesc restricted quotient ⟨folded, continuous_folded⟩ fibers
    (restricted lift) = b
  rw [quotientContinuousDesc_apply]
  exact Subtype.ext ((on_boundary lift ha).trans image)

theorem contractible_boundaryImage [T1Space X] (center : A) (outside : center ∉ Q.boundary)
    [ContractibleSpace ↥(({Q.projection center} : Set X)ᶜ)]
    (retract : C(↥(({center} : Set A)ᶜ), Q.boundary))
    (identity : ∀ b : Q.boundary, ∀ h : b.val ≠ center, retract ⟨b.val, h⟩ = b) :
    ContractibleSpace Q.boundaryImage := by
  obtain ⟨R, fixed⟩ := Q.exists_boundary_retraction center outside retract identity
  exact contractible_of_retraction (Q.boundaryImageInclusion center outside) R fixed

end BoundaryQuotient
end Unfoldings
