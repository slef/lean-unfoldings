module

public import Unfoldings.Source.ShortestPath
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Compactness of all shortest paths from a source

Use uniform convergence of the actual constant-speed paths, retaining every
tie. The source condition and distance equations are closed, and compactness
of the surface bounds every path's speed by one common diameter. Arzela--Ascoli
therefore makes the whole shortest-path space compact.
-/

@[expose] public section

open scoped ENNReal Topology BoundedContinuousFunction

noncomputable section

namespace Unfoldings.SourcePath

variable {X : Type*} [MetricSpace X] {source : X}

def toBounded (p : SourcePath source) : unitInterval →ᵇ X :=
  BoundedContinuousFunction.mkOfCompact p.path.toContinuousMap

theorem toBounded_injective : Function.Injective (toBounded (source := source)) := by
  intro p q equal
  exact SourcePath.ext (fun t => congrArg (fun f : unitInterval →ᵇ X => f t) equal)

instance : MetricSpace (SourcePath source) :=
  MetricSpace.induced toBounded toBounded_injective inferInstance

theorem toBounded_isometry : Isometry (toBounded (source := source)) := fun _ _ => rfl

theorem continuous_target : Continuous (SourcePath.target (source := source)) := by
  have continuous := (continuous_eval_const (1 : unitInterval)).comp
    (toBounded_isometry (source := source)).continuous
  have equal : (fun f : unitInterval →ᵇ X => f 1) ∘ toBounded =
      SourcePath.target (source := source) := funext (fun p => p.path.target)
  rwa [equal] at continuous

theorem continuous_evaluation : Continuous (fun p : SourcePath source × unitInterval =>
    p.1.path p.2) :=
  continuous_eval.comp (toBounded_isometry.continuous.prodMap continuous_id)

def normalizedPaths (source : X) : Set (unitInterval →ᵇ X) :=
  {f | f 0 = source ∧ ∀ s t, dist (f s) (f t) = dist source (f 1) * dist s t}

theorem range_toBounded : Set.range (toBounded (source := source)) = normalizedPaths source := by
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.path.source, fun s t => by
      simpa only [toBounded, BoundedContinuousFunction.mkOfCompact_apply,
        Path.coe_toContinuousMap, Path.target] using p.geodesic.dist_eq s t⟩
  · intro member
    let p : Path source (f 1) :=
      { toContinuousMap := f.toContinuousMap
        source' := member.1
        target' := rfl }
    have geodesic : p.IsGeodesic := by
      intro s t
      change edist (f s) (f t) = edist source (f 1) * edist s t
      rw [edist_dist, member.2 s t, ENNReal.ofReal_mul dist_nonneg,
        ← edist_dist, ← edist_dist]
    exact ⟨⟨f 1, p, geodesic⟩, by ext t; rfl⟩

theorem normalizedPaths_closed (source : X) : IsClosed (normalizedPaths source) := by
  have start : IsClosed {f : unitInterval →ᵇ X | f 0 = source} :=
    isClosed_eq (continuous_eval_const _) continuous_const
  have distances : IsClosed {f : unitInterval →ᵇ X |
      ∀ s t, dist (f s) (f t) = dist source (f 1) * dist s t} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun s => isClosed_iInter (fun t =>
      isClosed_eq ((continuous_eval_const s).dist (continuous_eval_const t))
        ((continuous_const.dist (continuous_eval_const _)).mul continuous_const)))
  exact start.inter distances

theorem normalizedPaths_compact [CompactSpace X] (source : X) :
    IsCompact (normalizedPaths source) := by
  apply BoundedContinuousFunction.arzela_ascoli₁ _ (normalizedPaths_closed source)
  apply Metric.equicontinuous_of_continuity_modulus
    (fun d => Metric.diam (Set.univ : Set X) * d)
    (by
      have continuous : Continuous (fun d : ℝ => Metric.diam (Set.univ : Set X) * d) :=
        continuous_const.mul continuous_id
      simpa only [mul_zero] using continuous.tendsto (0 : ℝ))
  intro s t f
  rw [f.property.2 s t]
  exact mul_le_mul_of_nonneg_right
    (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _))
    dist_nonneg

instance [CompactSpace X] : CompactSpace (SourcePath source) := by
  apply isCompact_univ_iff.mp
  rw [toBounded_isometry.isEmbedding.isInducing.isCompact_iff,
    Set.image_univ, range_toBounded]
  exact normalizedPaths_compact source

end Unfoldings.SourcePath
