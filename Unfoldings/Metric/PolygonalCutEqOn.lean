module

public import Unfoldings.Metric.PolygonalCutIsometricImage

/-! Cuts agreeing on the actual cells define the same original metric copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

section RelationCongr

variable {I : Type*} (E : I → Type*) [∀ i, EMetricSpace (E i)]
  {R S : Total E → Total E → Prop}

/-- Rewriting the declared seam relation preserves the realization and its metric. -/
def realizationRelationCongr (same : R = S) : Realization E R ≃ᵢ Realization E S := by
  cases same
  exact IsometryEquiv.refl _

@[simp] theorem realizationRelationCongr_point (same : R = S) (a : Total E) :
    realizationRelationCongr E same (point E R a) = point E S a := by
  cases same
  rfl

end RelationCongr

/-- The physical fold of a specified original cell copy is its actual spatial point. -/
theorem physicalSeams_fold_of {I X : Type*} [Finite I] [MetricSpace X]
    {cells : I → Set X} (S : PhysicalSeams cells) (i : I) (p : cells i) :
    S.fold (of (fun i => cells i) S.relation i p) = p.val := rfl

variable {E I : Type*} [NormedAddCommGroup E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (cuts other : Set E)
  (agree : ∀ i p, p ∈ cells i → (p ∈ cuts ↔ p ∈ other))

include agree

omit [Finite I] in
/-- Only the cut's intersection with actual physical cells affects its closed attachments. -/
theorem cutSeams_carrier_eq_of_eqOn (i j : I) :
    (cutSeams cells closed cuts).carrier i j = (cutSeams cells closed other).carrier i j := by
  apply congrArg closure
  ext p
  constructor
  · exact fun hp => ⟨hp.1, fun member => hp.2 ((agree i p hp.1.1).mpr member)⟩
  · exact fun hp => ⟨hp.1, fun member => hp.2 ((agree i p hp.1.1).mp member)⟩

theorem cutSeams_relation_iff_of_eqOn (a b : Total (fun i => cells i)) :
    (cutSeams cells closed cuts).relation a b ↔ (cutSeams cells closed other).relation a b := by
  rw [(cutSeams cells closed cuts).relation_iff,
    (cutSeams cells closed other).relation_iff,
    cutSeams_carrier_eq_of_eqOn cells closed cuts other agree]

/-- Changing the cut outside the actual patch preserves its complete cut metric and copies. -/
def polygonalCutEqOnEquiv : PolygonalCut cells closed cuts ≃ᵢ PolygonalCut cells closed other :=
  realizationRelationCongr (fun i => cells i) (funext fun a => funext fun b =>
    propext (cutSeams_relation_iff_of_eqOn cells closed cuts other agree a b))

@[simp] theorem polygonalCutEqOnEquiv_of (i : I) (x : cells i) :
    polygonalCutEqOnEquiv cells closed cuts other agree
      (of (fun i => cells i) (cutSeams cells closed cuts).relation i x) =
        of (fun i => cells i) (cutSeams cells closed other).relation i x :=
  realizationRelationCongr_point _ _ _

theorem fold_polygonalCutEqOnEquiv (x : PolygonalCut cells closed cuts) :
    (cutSeams cells closed other).fold (polygonalCutEqOnEquiv cells closed cuts other agree x) =
      (cutSeams cells closed cuts).fold x := by
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective (fun i => cells i)
    (cutSeams cells closed cuts).relation x
  calc
    _ = (cutSeams cells closed other).fold
        (of (fun i => cells i) (cutSeams cells closed other).relation i p) :=
      congrArg (cutSeams cells closed other).fold
        (polygonalCutEqOnEquiv_of cells closed cuts other agree i p)
    _ = p.val := physicalSeams_fold_of _ _ _
    _ = (cutSeams cells closed cuts).fold
        (of (fun i => cells i) (cutSeams cells closed cuts).relation i p) :=
      (physicalSeams_fold_of _ _ _).symm

end Unfoldings.MetricGluing
