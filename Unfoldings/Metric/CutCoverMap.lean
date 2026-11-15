module

public import Unfoldings.Metric.PolygonalCut

/-! Actual physical subcovers map into the original cut metric without changing spatial points. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I J : Type*} [NormedAddCommGroup E] [Finite I] [Finite J]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
  (target : J → Set E) (target_closed : ∀ j, IsClosed (target j))
  (index : I → J) (included : ∀ i, cells i ⊆ target (index i)) (cuts : Set E)

/-- A physical cell inclusion sends its original cut copy to that same physical target copy. -/
def cutCoverMap : PolygonalCut cells closed cuts → PolygonalCut target target_closed cuts :=
  lift (fun i => cells i) (cutSeams cells closed cuts).relation
    (fun i x => of (fun j => target j) (cutSeams target target_closed cuts).relation (index i)
      ⟨x.val, included i x.property⟩) (fun i x y => by
      simpa only [Subtype.edist_eq, ENNReal.coe_one, one_mul] using
        edist_of_le (fun j => target j) (cutSeams target target_closed cuts).relation (index i)
          ⟨x.val, included i x.property⟩ ⟨y.val, included i y.property⟩)
    (by
      rintro a b ⟨⟨i, j⟩, x, rfl, rfl⟩
      apply point_eq_of_glue
      refine ⟨(index i, index j), ⟨x.val, ?_⟩, rfl, rfl⟩
      apply closure_mono ?_ x.property
      intro z hz
      exact ⟨⟨included i hz.1.1, included j hz.1.2⟩, hz.2⟩)

@[simp] theorem cutCoverMap_of (i : I) (x : cells i) :
    cutCoverMap cells closed target target_closed index included cuts
      (of (fun i => cells i) (cutSeams cells closed cuts).relation i x) =
      of (fun j => target j) (cutSeams target target_closed cuts).relation (index i)
        ⟨x.val, included i x.property⟩ := rfl

theorem cutCoverMap_lipschitz :
    LipschitzWith 1 (cutCoverMap cells closed target target_closed index included cuts) :=
  lift_lipschitz _ _ _ _ _

@[simp] theorem fold_cutCoverMap (x : PolygonalCut cells closed cuts) :
    (cutSeams target target_closed cuts).fold
      (cutCoverMap cells closed target target_closed index included cuts x) =
        (cutSeams cells closed cuts).fold x := by
  obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation x
  rfl

/-- Exact ambient distances in a physical subcover also hold in the entire original cut. -/
theorem cutCoverMap_isometry (source_isometry : Isometry (cutSeams cells closed cuts).fold) :
    Isometry (cutCoverMap cells closed target target_closed index included cuts) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      cutCoverMap_lipschitz cells closed target target_closed index included cuts x y
  · have bound := (cutSeams target target_closed cuts).fold_lipschitz
      (cutCoverMap cells closed target target_closed index included cuts x)
      (cutCoverMap cells closed target target_closed index included cuts y)
    rw [fold_cutCoverMap, fold_cutCoverMap, source_isometry.edist_eq] at bound
    simpa only [ENNReal.coe_one, one_mul] using bound

end Unfoldings.MetricGluing
