module

public import Unfoldings.Metric.CutIsometricCoverMap

/-! Rigidly placed complete planar covers give the actual physical cut metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing

variable {E F I : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [NormedAddCommGroup F] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
  (f : E → F) (isometric : Isometry f)
  (target : I → Set F) (target_closed : ∀ i, IsClosed (target i))
  (images : ∀ i, f '' cells i = target i) (cuts : Set F)

include images in
/-- Exact physical images cover every original metric copy, without a surjectivity certificate. -/
theorem cutIsometricCoverMap_surjective_of_images
    (included : ∀ i, f '' cells i ⊆ target i) :
    Function.Surjective
      (cutIsometricCoverMap cells closed f isometric target target_closed id included cuts) := by
  intro y
  obtain ⟨⟨i, p⟩, rfl⟩ := point_surjective (fun i => target i)
    (cutSeams target target_closed cuts).relation y
  have member : p.val ∈ f '' cells i := Eq.mpr
    (congrArg (fun s : Set F => p.val ∈ s) (images i)) p.property
  obtain ⟨x, hx, equal⟩ := member
  refine ⟨of (fun i => cells i) (cutSeams cells closed (f ⁻¹' cuts)).relation i ⟨x, hx⟩, ?_⟩
  exact (cutIsometricCoverMap_of cells closed f isometric target target_closed id included
    cuts i ⟨x, hx⟩).trans
      (congrArg (of (fun i => target i) (cutSeams target target_closed cuts).relation i)
        (Subtype.ext equal))

include isometric images in
/-- An exact flat cut metric remains exact after its rigid physical placement.
Every physical cut copy is supplied by its original planar cell. -/
theorem cut_fold_isometry_of_isometric_images
    (source_isometry : Isometry (cutSeams cells closed (f ⁻¹' cuts)).fold) :
    Isometry (cutSeams target target_closed cuts).fold := by
  have included : ∀ i, f '' cells i ⊆ target i := fun i x hx =>
    Eq.mp (congrArg (fun s : Set F => x ∈ s) (images i)) hx
  let map := cutIsometricCoverMap cells closed f isometric target target_closed id included cuts
  have onto := cutIsometricCoverMap_surjective_of_images cells closed f isometric
    target target_closed images cuts included
  have exact_map := cutIsometricCoverMap_isometry cells closed f isometric
    target target_closed id included cuts source_isometry
  intro x y
  obtain ⟨u, rfl⟩ := onto x
  obtain ⟨v, rfl⟩ := onto y
  exact (congrArg₂ edist
    (fold_cutIsometricCoverMap cells closed f isometric target target_closed id included cuts u)
    (fold_cutIsometricCoverMap cells closed f isometric
      target target_closed id included cuts v)).trans
      ((isometric.edist_eq _ _).trans
        ((source_isometry.edist_eq u v).trans (exact_map.edist_eq u v).symm))

end Unfoldings.MetricGluing
