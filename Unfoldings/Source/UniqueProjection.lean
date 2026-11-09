module

public import Unfoldings.Source.CutLocus
public import Unfoldings.Source.CompactPaths
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuous shortest-path selection off the closed cut locus

Endpoint evaluation on the compact space of all shortest paths is closed.
Over the cut-locus complement its fibers are singletons. Restriction is
therefore a homeomorphism, proving continuity of the unique path without
assuming a choice function is continuous.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourcePath

variable {X : Type*} [MetricSpace X] {source : X}

theorem eq_of_target_eq_off_cutLocus {p q : SourcePath source}
    (outside : p.target ∉ sourceCutLocus source) (equal : p.target = q.target) : p = q := by
  obtain ⟨a, p, geodesic⟩ := p
  obtain ⟨b, q, other⟩ := q
  change a = b at equal
  subst b
  have same : p = q := geodesic_unique_off_cutLocus outside geodesic other
  subst q
  rfl

theorem target_injective_off_cutLocus :
    Function.Injective (((sourceCutLocus source)ᶜ).restrictPreimage
      (SourcePath.target (source := source))) := by
  intro p q equal
  apply Subtype.ext
  exact eq_of_target_eq_off_cutLocus p.property (congrArg Subtype.val equal)

def offCutLocusHomeomorph [CompactSpace X]
    (exists_paths : Function.Surjective (SourcePath.target (source := source))) :
    {p : SourcePath source // p.target ∉ sourceCutLocus source} ≃ₜ
      ↥((sourceCutLocus source)ᶜ) := by
  let f := ((sourceCutLocus source)ᶜ).restrictPreimage (SourcePath.target (source := source))
  have onto : Function.Surjective f := by
    intro x
    obtain ⟨p, equal⟩ := exists_paths x.val
    have outside : p.target ∉ sourceCutLocus source := by rw [equal]; exact x.property
    exact ⟨⟨p, outside⟩, Subtype.ext equal⟩
  exact (Equiv.ofBijective f ⟨target_injective_off_cutLocus, onto⟩).toHomeomorphOfContinuousClosed
    continuous_target.restrictPreimage (continuous_target.isClosedMap.restrictPreimage _)

@[simp] theorem offCutLocusHomeomorph_apply [CompactSpace X]
    (exists_paths : Function.Surjective (SourcePath.target (source := source)))
    (p : {p : SourcePath source // p.target ∉ sourceCutLocus source}) :
    (offCutLocusHomeomorph exists_paths p).val = p.val.target := rfl

end Unfoldings.SourcePath
