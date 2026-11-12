module

public import Unfoldings.Complex.FaceRestriction
public import Unfoldings.Complex.Classes

/-! Full-face restrictions preserve every retained nonvertex point identification. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
def includedTotal (U : Set Face) (a : (C.restrictFaces U).Total) : C.Total :=
  ⟨a.1.val, a.2⟩

open Classical in
theorem includedTotal_injective (U : Set Face) : Function.Injective (C.includedTotal U) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ equal
  have faces : a = b := Subtype.ext (congrArg Sigma.fst equal)
  subst b
  have points : x = y := Subtype.ext (congrArg (fun a : C.Total => a.2.val) equal)
  subst y
  rfl

open Classical in
theorem restrict_glue_of_included (U : Set Face) (retain : Set C.Seam)
    {a b : (C.restrictFaces U).Total}
    (joined : C.glue retain (C.includedTotal U a) (C.includedTotal U b)) :
    (C.restrictFaces U).glue (C.restrictRetain U retain) a b := by
  obtain ⟨s, kept, x, first, last⟩ := joined
  have first_mem : (C.left s).face ∈ U := by
    have faces := congrArg Sigma.fst first
    change a.1.val = (C.left s).face at faces
    exact faces ▸ a.1.property
  have last_mem : (C.right s).face ∈ U := by
    have faces := congrArg Sigma.fst last
    change b.1.val = (C.right s).face at faces
    exact faces ▸ b.1.property
  let t : (C.restrictFaces U).Seam := ⟨s, first_mem, last_mem⟩
  refine ⟨t, kept, x, ?_, ?_⟩
  · exact C.includedTotal_injective U first
  · exact C.includedTotal_injective U last

open Classical in
theorem restrict_eqvGen_of_regular (U : Set Face) (retain : Set C.Seam)
    {a b : (C.restrictFaces U).Total} (regular : ¬ (C.restrictFaces U).IsVertex a)
    (related : Relation.EqvGen (C.glue retain) (C.includedTotal U a) (C.includedTotal U b)) :
    Relation.EqvGen ((C.restrictFaces U).glue (C.restrictRetain U retain)) a b := by
  change ¬ C.IsVertex (C.includedTotal U a) at regular
  rcases (C.eqvGen_iff_of_regular retain regular).mp related with equal | crossing
  · have same := C.includedTotal_injective U equal
    rw [same]
    exact Relation.EqvGen.refl _
  · rcases (C.crosses_iff retain _ _).mp crossing with forward | backward
    · exact Relation.EqvGen.rel _ _ (C.restrict_glue_of_included U retain forward)
    · exact (Relation.EqvGen.rel _ _ (C.restrict_glue_of_included U retain backward)).symm

end Unfoldings.TriangleComplex
