module

public import Unfoldings.Complex.Folding

/-! Original retained triangle classes agree at every physical point away from removed seams. -/

@[expose] public section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

/-- Actual retained attachment chains preserve their original spatial point. -/
theorem place_eq_of_eqvGen {retain : Set C.Seam} {a b : C.Total}
    (related : Relation.EqvGen (C.glue retain) a b) :
    F.place a.1 a.2.val = F.place b.1 b.2.val :=
  congrArg (F.toSpace retain) (MetricGluing.point_eq_of_eqvGen C.Cell related)

/-- Away from the physical cut, every original full attachment chain uses only retained seams. -/
theorem retained_eqvGen_of_full_outside (retain : Set C.Seam) (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts)
    {a b : C.Total} (related : Relation.EqvGen (C.glue Set.univ) a b)
    (outside : F.place a.1 a.2.val ∉ cuts) : Relation.EqvGen (C.glue retain) a b := by
  induction related with
  | rel a b joined =>
    obtain ⟨s, _, x, rfl, rfl⟩ := joined
    apply Relation.EqvGen.rel
    refine ⟨s, ?_, x, rfl, rfl⟩
    by_contra absent
    exact outside (removed s absent x)
  | refl => exact Relation.EqvGen.refl _
  | symm a b related ih =>
    have physical := F.place_eq_of_eqvGen related
    apply Relation.EqvGen.symm
    exact ih (fun member => outside
      (Eq.mp (congrArg (fun z : Space => z ∈ cuts) physical) member))
  | trans a b c first last ih_first ih_last =>
    have physical := F.place_eq_of_eqvGen first
    exact Relation.EqvGen.trans _ _ _ (ih_first outside)
      (ih_last (fun member => outside
        (Eq.mpr (congrArg (fun z : Space => z ∈ cuts) physical) member)))

/-- Embeddedness identifies actual original retained metric copies at an uncut physical point. -/
theorem retained_related_of_spatial_eq_outside (embedded : F.IsEmbedded)
    (retain : Set C.Seam) (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts)
    (a b : C.Total) (same : F.place a.1 a.2.val = F.place b.1 b.2.val)
    (outside : F.place a.1 a.2.val ∉ cuts) : Relation.EqvGen (C.glue retain) a b :=
  F.retained_eqvGen_of_full_outside retain cuts removed
    ((F.isEmbedded_iff.mp embedded) a b same) outside

theorem faceMap_eq_of_spatial_eq_outside (embedded : F.IsEmbedded)
    (retain : Set C.Seam) (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts)
    {f g : Face} (x : C.Cell f) (y : C.Cell g) (same : F.place f x.val = F.place g y.val)
    (outside : F.place f x.val ∉ cuts) : C.faceMap retain f x = C.faceMap retain g y :=
  MetricGluing.point_eq_of_eqvGen C.Cell
    (F.retained_related_of_spatial_eq_outside embedded retain cuts removed
      ⟨f, x⟩ ⟨g, y⟩ same outside)

end Unfoldings.SpatialFolding
