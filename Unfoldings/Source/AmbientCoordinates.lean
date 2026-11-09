module

public import Unfoldings.Source.ActualCut

/-!
# Extending the retained source-coordinate function for local chart arguments

Only its proved agreement on the cut complement is used. The extension is
assigned zero elsewhere; all shortest-path boundary copies remain represented
by the existing completed source domain and are not replaced by this function.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

def extendedSourceCoordinates :
    letI := P.metricSpace
    {source : C.Realization Set.univ} → SourceFrame source → C.Realization Set.univ → Plane := by
  let := P.metricSpace
  intro source R
  exact Function.extend Subtype.val
    (R.coordinatesOffCutLocus (P.sourcePath_target_surjective source)) (fun _ => 0)

theorem extendedSourceCoordinates_agrees :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : ↥((sourceCutLocus source)ᶜ)),
      P.extendedSourceCoordinates R x.val =
        R.coordinatesOffCutLocus (P.sourcePath_target_surjective source) x := by
  let := P.metricSpace
  intro source R x
  change Function.extend Subtype.val
    (R.coordinatesOffCutLocus (P.sourcePath_target_surjective source)) (fun _ => 0) x.val = _
  exact Subtype.val_injective.extend_apply _ _ x

theorem source_isometry_ambient_neighborhood :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source)
      (x : ↥((sourceCutLocus source)ᶜ)),
      ∃ S : Set (C.Realization Set.univ), IsOpen S ∧ x.val ∈ S ∧
        S ⊆ (sourceCutLocus source)ᶜ ∧
          Isometry (fun y : S => P.extendedSourceCoordinates R y.val) := by
  let := P.metricSpace
  intro source R x
  obtain ⟨S, open_S, inside, isometry⟩ := P.source_coordinates_local_isometry R x
  let T := Subtype.val '' S
  have open_T : IsOpen T :=
    (isClosed_sourceCutLocus source).isOpen_compl.isOpenMap_subtype_val S open_S
  refine ⟨T, open_T, ⟨x, inside, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, _member, rfl⟩
    exact y.property
  · intro a b
    obtain ⟨p, hp, first⟩ := a.property
    obtain ⟨q, hq, last⟩ := b.property
    change edist (P.extendedSourceCoordinates R a.val) (P.extendedSourceCoordinates R b.val) =
      edist a.val b.val
    rw [← first, ← last, P.extendedSourceCoordinates_agrees R p,
      P.extendedSourceCoordinates_agrees R q]
    exact isometry ⟨p, hp⟩ ⟨q, hq⟩

end Unfoldings.SpatialFolding.ConvexBoundary
