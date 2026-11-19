module

public import Unfoldings.Metric.ClosedSeamsTopology
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Compatible continuous cell maps descend to the exact intrinsic closed-seam quotient. -/

@[expose] public section

noncomputable section

namespace Unfoldings.MetricGluing.ClosedSeams

variable {I : Type*} [Finite I] {E : I → Type*} [∀ i, MetricSpace (E i)]
  (S : ClosedSeams E) (finite : ∀ a i, (classIn E S.relation a i).Finite)
  {Y : Type*} [TopologicalSpace Y] (f : ∀ i, E i → Y)
  (compatible : ∀ a b, S.relation a b → f a.1 a.2 = f b.1 b.2)

/-- The closed-seam realization has its original topological gluing universal property. -/
def continuousLift : Realization E S.relation → Y :=
  (Quot.lift (fun a : Total E => f a.1 a.2) compatible) ∘ (S.seamHomeomorph finite).symm

theorem continuous_continuousLift (continuous : ∀ i, Continuous (f i)) :
    Continuous (S.continuousLift finite f compatible) :=
  (continuous_quot_lift compatible (continuous_sigma continuous)).comp
    (S.seamHomeomorph finite).symm.continuous

omit [TopologicalSpace Y] in
@[simp] theorem continuousLift_point (a : Total E) :
    S.continuousLift finite f compatible (point E S.relation a) = f a.1 a.2 := by
  rw [← S.seamHomeomorph_seamPoint finite a]
  change (Quot.lift (fun a : Total E => f a.1 a.2) compatible)
    ((S.seamHomeomorph finite).symm ((S.seamHomeomorph finite) (seamPoint E S.relation a))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- A finite closed-seam gluing of proper cell maps is proper on the entire realization. -/
theorem isProperMap_continuousLift [T2Space Y] [CompactlyCoherentSpace Y]
    (proper : ∀ i, IsProperMap (f i)) :
    IsProperMap (S.continuousLift finite f compatible) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨S.continuous_continuousLift finite f compatible (fun i => (proper i).continuous), ?_⟩
  intro K compact
  let image (i : I) := of E S.relation i '' (f i ⁻¹' K)
  have cover : (S.continuousLift finite f compatible) ⁻¹' K = ⋃ i, image i := by
    ext x
    obtain ⟨⟨i, y⟩, rfl⟩ := point_surjective E S.relation x
    constructor
    · intro hx
      have member : f i y ∈ K := by
        change S.continuousLift finite f compatible (point E S.relation ⟨i, y⟩) ∈ K at hx
        rwa [S.continuousLift_point] at hx
      exact Set.mem_iUnion.mpr ⟨i, y, member, rfl⟩
    · rintro hx
      obtain ⟨j, z, inside, equal⟩ := Set.mem_iUnion.mp hx
      change S.continuousLift finite f compatible (point E S.relation ⟨i, y⟩) ∈ K
      rw [← equal]
      exact (S.continuousLift_point finite f compatible ⟨j, z⟩).symm ▸ inside
  rw [cover]
  exact isCompact_iUnion (fun i => ((proper i).isCompact_preimage compact).image
    (of_lipschitz E S.relation i).continuous)

end Unfoldings.MetricGluing.ClosedSeams
