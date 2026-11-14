module

public import Unfoldings.Metric.FinitePlanarDevelopment
public import Unfoldings.Metric.EuclideanLocalHomeomorph
public import Unfoldings.Metric.EuclideanDevelopment
public import Unfoldings.Metric.BoundaryCellDevelopment

/-! Simply connected flat boundary gluings of finite closed convex planar cells develop globally. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

universe u

variable {I : Type u} [Finite I] (cells : I → Set Plane)
  (glue : Total (fun i => cells i) → Total (fun i => cells i) → Prop)
  [SimplyConnectedSpace (Realization (fun i => cells i) glue)]
  [LocallyPathConnectedSpace (Realization (fun i => cells i) glue)]

local instance flatPlanarGluingMetricSpace : MetricSpace (Realization (fun i => cells i) glue) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

/-- The cells may be unbounded. Boundary-only gluing, actual local Euclidean regularity,
and simple connectedness suffice; neither a development nor nonoverlap is assumed. -/
theorem exists_global_planar_isometry
    (closed : ∀ i, IsClosed (cells i)) (convex : ∀ i, Convex ℝ (cells i))
    (full : ∀ i, (interior (cells i)).Nonempty)
    (boundary : ∀ i x, x ∈ seamSupport (fun i => cells i) glue i →
      x.val ∉ interior (cells i))
    (regular : ∀ x : Realization (fun i => cells i) glue, HasMetricBallChart Plane x) :
    ∃ f : Realization (fun i => cells i) glue → Plane, Isometry f ∧ Function.Surjective f := by
  let complete (i : I) : CompleteSpace (cells i) := (closed i).isComplete.completeSpace_coe
  let A := EuclideanAtlas.ofRegular regular
  let root : Realization (fun i => cells i) glue := Classical.choice inferInstance
  obtain ⟨f, local_isometry⟩ := A.exists_local_isometry root ⟨AffineIsometryEquiv.refl ℝ Plane⟩
  have local_homeomorph := A.isLocalHomeomorph_of_local_isometry f local_isometry
  have cell_isometric (i : I) : Isometry (f ∘ of (fun i => cells i) glue i) :=
    cell_isometry_of_boundary_gluing cells glue f local_homeomorph.continuous local_isometry
      i (convex i) (full i) (boundary i)
  have isometry := isometry_of_localHomeomorph_isometric_cells (fun i => cells i) glue
    f cell_isometric local_homeomorph
  have cover : ∀ x : Realization (fun i => cells i) glue,
      ∃ i, ∃ p : cells i, of (fun i => cells i) glue i p = x := by
    intro x
    obtain ⟨⟨i, p⟩, equal⟩ := point_surjective (fun i => cells i) glue x
    exact ⟨i, p, equal⟩
  have covering := isCoveringMap_of_finite_complete_cells (fun i => cells i)
    (of (fun i => cells i) glue) (fun i => (of_lipschitz (fun i => cells i) glue i).continuous)
    cover f cell_isometric local_homeomorph
  exact ⟨f, isometry, (coveringHomeomorphOfSimplyConnected covering).surjective⟩

end Unfoldings.MetricGluing
