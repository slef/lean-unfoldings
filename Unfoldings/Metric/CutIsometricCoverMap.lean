module

public import Unfoldings.Metric.CutCoverMap
public import Unfoldings.Metric.PolygonalCutIsometricImage
public import Unfoldings.Metric.PolygonalBoundaryCuts

/-! Rigid planar subcovers embed in full physical cuts with their exact intrinsic metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E F I J : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace E]
  [Finite I] [Finite J]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i)) (f : E → F) (isometric : Isometry f)
  (target : J → Set F) (target_closed : ∀ j, IsClosed (target j))
  (index : I → J) (included : ∀ i, f '' cells i ⊆ target (index i)) (cuts : Set F)

/-- Place a planar cut subcover into its actual cells of the full physical cut. -/
def cutIsometricCoverMap :
    PolygonalCut cells closed (f ⁻¹' cuts) → PolygonalCut target target_closed cuts :=
  cutCoverMap (fun i => f '' cells i) (isClosed_isometricImageCell cells closed f isometric)
    target target_closed index included cuts ∘ cutIsometricImageEquiv cells closed f isometric cuts


@[simp] theorem cutIsometricCoverMap_of (i : I) (x : cells i) :
    cutIsometricCoverMap cells closed f isometric target target_closed index included cuts
      (of (fun i => cells i) (cutSeams cells closed (f ⁻¹' cuts)).relation i x) =
      of (fun j => target j) (cutSeams target target_closed cuts).relation (index i)
        ⟨f x.val, included i ⟨x.val, x.property, rfl⟩⟩ := by
  rw [cutIsometricCoverMap, Function.comp_apply, cutIsometricImageEquiv_of, cutCoverMap_of]
  rfl

theorem cutIsometricCoverMap_lipschitz :
    LipschitzWith 1
      (cutIsometricCoverMap cells closed f isometric target target_closed index included cuts) := by
  simpa only [one_mul, cutIsometricCoverMap] using (cutCoverMap_lipschitz (fun i => f '' cells i)
    (isClosed_isometricImageCell cells closed f isometric) target target_closed index included
    cuts).comp
    (cutIsometricImageEquiv cells closed f isometric cuts).isometry.lipschitzWith

@[simp] theorem fold_cutIsometricCoverMap (x : PolygonalCut cells closed (f ⁻¹' cuts)) :
    (cutSeams target target_closed cuts).fold
      (cutIsometricCoverMap cells closed f isometric target target_closed index included cuts x) =
        f ((cutSeams cells closed (f ⁻¹' cuts)).fold x) := by
  rw [cutIsometricCoverMap, Function.comp_apply, fold_cutCoverMap, fold_cutIsometricImageEquiv]

/-- An exact flat physical subcover has its same metric in the full physical cut. -/
theorem cutIsometricCoverMap_isometry
    (source_isometry : Isometry (cutSeams cells closed (f ⁻¹' cuts)).fold) :
    Isometry
      (cutIsometricCoverMap cells closed f isometric target target_closed index included cuts) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      cutIsometricCoverMap_lipschitz cells closed f isometric target target_closed index included
        cuts x y
  · have bound := (cutSeams target target_closed cuts).fold_lipschitz
      (cutIsometricCoverMap cells closed f isometric target target_closed index included cuts x)
      (cutIsometricCoverMap cells closed f isometric target target_closed index included cuts y)
    rw [fold_cutIsometricCoverMap, fold_cutIsometricCoverMap, isometric.edist_eq,
      source_isometry.edist_eq] at bound
    simpa only [ENNReal.coe_one, one_mul] using bound

variable [NormedSpace ℝ E]

omit [NormedAddCommGroup F] [CompleteSpace E] in
/-- Boundary cuts of a convex full-dimensional cover supply the required exact physical metric. -/
theorem cut_fold_isometry_of_boundary_cuts {s : Set E} (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty) (cover : s = ⋃ i, cells i)
    (convex_s : Convex ℝ s) (cut_closed : IsClosed (f ⁻¹' cuts))
    (outside : Disjoint (interior s) (f ⁻¹' cuts)) :
    Isometry (cutSeams cells closed (f ⁻¹' cuts)).fold := by
  have positions (z : PolygonalCut cells closed (f ⁻¹' cuts)) :
      (cutSeams cells closed (f ⁻¹' cuts)).fold z =
        (cutToPolygonal cells closed (f ⁻¹' cuts) convex cover z).val := by
    obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i)
      (cutSeams cells closed (f ⁻¹' cuts)).relation z
    rfl
  intro x y
  rw [positions x, positions y]
  have exact_distance := cutToPolygonal_isometry_of_boundary_cuts cells closed (f ⁻¹' cuts)
    convex full cover convex_s cut_closed outside x y
  rw [PolygonalPoint.edist_eq_of_segment (convex_s.segment_subset
    (cutToPolygonal cells closed (f ⁻¹' cuts) convex cover x).property
    (cutToPolygonal cells closed (f ⁻¹' cuts) convex cover y).property)] at exact_distance
  exact exact_distance

end Unfoldings.MetricGluing
