module

public import Unfoldings.Topology.LocalPush
public import Unfoldings.Topology.BoundaryQuotient
public import Unfoldings.Topology.SmallHalfPlanePush

/-!
# Inward embeddings from actual half-plane boundary charts

Local half-plane charts identify a specified boundary with the boundary line.
The explicit compactly supported pushes transfer through these charts and
extend by the identity. On a compact Hausdorff space their finite composition
embeds the entire space into its boundary complement.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open PlanarTopology

variable {X : Type*} [TopologicalSpace X] (B : Set X) (x : X)

structure HalfPlaneBoundaryChart where
  source : Set X
  open_source : IsOpen source
  mem_source : x ∈ source
  target : Set closedHalfPlane
  open_target : IsOpen target
  chart : source ≃ₜ target
  center : (chart ⟨x, mem_source⟩).val = halfPlaneOrigin
  boundary : ∀ p : source, p.val ∈ B ↔ (chart p).val ∈ halfPlaneBoundary

namespace BoundaryPush.Local

variable {B x} {U : Set X} (P : BoundaryPush.Local (B := B) U x)

theorem mapsTo_chart : Set.MapsTo P.push.map U U := by
  intro y hy
  by_cases inside : y ∈ P.support
  · exact P.support_subset (P.invariant_support inside)
  · simpa only [P.fixed_outside y inside] using hy

end BoundaryPush.Local

namespace HalfPlaneBoundaryChart

variable {B x} [T2Space X] (A : HalfPlaneBoundaryChart B x)

include A in
theorem exists_boundaryPush : ∃ f : BoundaryPush B,
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ B ⊆ f.moved := by
  have target_center : halfPlaneOrigin ∈ A.target := by
    rw [← A.center]
    exact (A.chart ⟨x, A.mem_source⟩).property
  obtain ⟨P⟩ := exists_smallHalfPlanePush A.target A.open_target target_center
  let targetPush := P.push.restrict A.target P.mapsTo_chart
  let chartPush := targetPush.transport (Subtype.val ⁻¹' B : Set A.source) A.chart.symm (by
    intro p
    change p.val ∈ halfPlaneBoundary ↔ (A.chart.symm p).val ∈ B
    have boundary := (A.boundary (A.chart.symm p)).symm
    simpa only [Homeomorph.apply_symm_apply] using boundary)
  let K : Set A.target := Subtype.val ⁻¹' P.support
  have compact_K : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' P.compact_support
    intro p hp
    exact ⟨⟨p, P.support_subset hp⟩, rfl⟩
  let ambientSupport := (fun p : A.target => (A.chart.symm p).val) '' K
  have compact_support : IsCompact ambientSupport :=
    compact_K.image (continuous_subtype_val.comp A.chart.symm.continuous)
  have contained : ambientSupport ⊆ A.source := by
    rintro _ ⟨p, _, rfl⟩
    exact (A.chart.symm p).property
  have fixed (p : A.source) (outside : p.val ∉ ambientSupport) : chartPush.map p = p := by
    have original : (A.chart p).val ∉ P.support := by
      intro inside
      apply outside
      refine ⟨A.chart p, inside, ?_⟩
      exact congrArg Subtype.val (A.chart.symm_apply_apply p)
    have target_fixed : targetPush.map (A.chart p) = A.chart p :=
      Subtype.ext (P.fixed_outside _ original)
    change A.chart.symm (targetPush.map (A.chart p)) = p
    rw [target_fixed, Homeomorph.symm_apply_apply]
  let f := BoundaryPush.ofLocal B A.open_source chartPush ambientSupport
    compact_support.isClosed contained fixed
  let W : Set X := Subtype.val ''
    (A.chart ⁻¹' (Subtype.val ⁻¹' P.neighborhood : Set A.target))
  have open_W : IsOpen W := A.open_source.isOpenMap_subtype_val _
    (((P.open_neighborhood.preimage continuous_subtype_val).preimage A.chart.continuous))
  have center : x ∈ W := by
    refine ⟨⟨x, A.mem_source⟩, ?_, rfl⟩
    change (A.chart ⟨x, A.mem_source⟩).val ∈ P.neighborhood
    rw [A.center]
    exact P.mem_neighborhood
  refine ⟨f, W, open_W, center, ?_⟩
  rintro y ⟨⟨p, near, rfl⟩, boundary⟩
  refine ⟨boundary, ?_⟩
  have target_moved : targetPush.map (A.chart p) ∉
      (Subtype.val ⁻¹' halfPlaneBoundary : Set A.target) :=
    (P.moves_neighborhood ⟨near, (A.boundary p).mp boundary⟩).2
  have coordinates : A.chart (chartPush.map p) = targetPush.map (A.chart p) :=
    A.chart.apply_symm_apply _
  change extendLocalByIdentity A.source chartPush.map p.val ∉ B
  rw [extendLocalByIdentity_apply]
  intro still_boundary
  have image_boundary := (A.boundary (chartPush.map p)).mp still_boundary
  rw [coordinates] at image_boundary
  exact target_moved image_boundary

end HalfPlaneBoundaryChart

/-- Compact spaces with genuine half-plane boundary charts embed into their interiors. -/
theorem exists_inward_embedding_of_halfPlaneCharts [CompactSpace X] [T2Space X]
    (compact : IsCompact B) (charts : ∀ x ∈ B, Nonempty (HalfPlaneBoundaryChart B x)) :
    ∃ f : C(X, X), Topology.IsClosedEmbedding f ∧ Set.range f ⊆ Bᶜ := by
  apply BoundaryPush.exists_embedding_misses_boundary compact
  intro x hx
  obtain ⟨A⟩ := charts x hx
  exact A.exists_boundaryPush

namespace BoundaryQuotient

variable {A Y : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]
  [TopologicalSpace Y] [T2Space Y] (Q : BoundaryQuotient A Y)

/-- Pushing the banks inward separates every fiber of the boundary quotient. -/
theorem exists_embedding_avoiding_boundaryImage
    (compact : IsCompact Q.boundary)
    (charts : ∀ x ∈ Q.boundary, Nonempty (HalfPlaneBoundaryChart Q.boundary x)) :
    ∃ f : C(A, Y), Topology.IsClosedEmbedding f ∧ Set.range f ⊆ Q.boundaryImageᶜ := by
  obtain ⟨push, embedding, misses⟩ :=
    exists_inward_embedding_of_halfPlaneCharts Q.boundary compact charts
  let f := Q.projection.comp push
  have injective : Function.Injective f := by
    intro a b equal
    rcases Q.fibers (push a) (push b) equal with same | both
    · exact embedding.injective same
    · exact (misses ⟨a, rfl⟩ both.1).elim
  refine ⟨f, f.continuous.isClosedEmbedding injective, ?_⟩
  rintro _ ⟨a, rfl⟩ boundary
  exact misses ⟨a, rfl⟩ ((Q.projection_mem_boundaryImage_iff (push a)).mp boundary)

end BoundaryQuotient

end Unfoldings
