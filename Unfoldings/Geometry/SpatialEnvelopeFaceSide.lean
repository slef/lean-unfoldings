module

public import Unfoldings.Geometry.SpatialEnvelopePartition
public import Unfoldings.Geometry.AffineSupportBoundary

/-! Actual cells on one support side cover the entire corresponding convex face region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The complete active region of an actual support, restricted to the anchor cell's side. -/
def faceSideRegion (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool) : Set Plane :=
  AffineEnvelope.cell (fun i => (family i).height) (P.support anchor) ∩
    {x | 0 ≤ AffineArrangement.signed f (signs anchor) x}

/-- All actual cells using the same physical support height on this chosen cut side. -/
abbrev FaceSideIndex (anchor : A) (signs : A → Bool) :=
  {a : A // (family (P.support a)).height = (family (P.support anchor)).height ∧
    signs a = signs anchor}

omit [Finite A] in
theorem convex_faceSideRegion (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool) :
    Convex ℝ (P.faceSideRegion anchor f signs) :=
  (AffineEnvelope.convex_cell _ _).inter ((convex_Ici (0 : ℝ)).affine_preimage _)

omit [Finite A] in
theorem isClosed_faceSideRegion (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (signs : A → Bool) :
    IsClosed (P.faceSideRegion anchor f signs) :=
  (AffineEnvelope.isClosed_cell _ _).inter
    (isClosed_le continuous_const
      (AffineArrangement.signed f (signs anchor)).continuous_of_finiteDimensional)

/-- Full-dimensional actual cells determine both their active support and their cut side
from any open intersection with the corresponding face-side region. -/
theorem faceSideRegion_eq_iUnion (anchor : A) (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a → 0 ≤ AffineArrangement.signed f (signs a) x) :
    P.faceSideRegion anchor f signs = ⋃ a : P.FaceSideIndex anchor signs, P.footprint a.val := by
  classical
  have cell_subset (a : P.FaceSideIndex anchor signs) :
      P.footprint a.val ⊆ P.faceSideRegion anchor f signs := by
    intro x member
    refine ⟨(AffineEnvelope.mem_cell_iff _ _ _).mpr ?_, ?_⟩
    · exact (P.active a.val x member).trans (congrArg (fun h : Plane →ᵃ[ℝ] ℝ => h x) a.property.1)
    · change 0 ≤ AffineArrangement.signed f (signs anchor) x
      simpa only [a.property.2] using aligned a.val x member
  have anchor_subset : P.footprint anchor ⊆ P.faceSideRegion anchor f signs := by
    intro x member
    exact ⟨(AffineEnvelope.mem_cell_iff _ _ _).mpr (P.active anchor x member),
      aligned anchor x member⟩
  have full_region : (interior (P.faceSideRegion anchor f signs)).Nonempty :=
    (P.full anchor).mono (interior_mono anchor_subset)
  have signed_proper : AffineArrangement.signed f (signs anchor) ≠ 0 := by
    cases value : signs anchor <;> simpa only [AffineArrangement.signed, value,
      Bool.false_eq_true, ↓reduceIte, neg_ne_zero] using proper
  have interior_covered : interior (P.faceSideRegion anchor f signs) ⊆
      ⋃ a : P.FaceSideIndex anchor signs, P.footprint a.val := by
    intro x inside
    have covered : x ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ x
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp covered
    have approached : x ∈ closure (interior (P.footprint a)) := by
      rw [(P.convex a).closure_interior_eq_closure_of_nonempty_interior (P.full a),
        (P.closed a).closure_eq]
      exact member
    obtain ⟨ε, positive, near⟩ := Metric.isOpen_iff.mp isOpen_interior x inside
    obtain ⟨c, interior_c, close⟩ := Metric.mem_closure_iff.mp approached ε positive
    have region_c : c ∈ interior (P.faceSideRegion anchor f signs) :=
      near (Metric.mem_ball.mpr (by rwa [dist_comm]))
    have height_eq : (family (P.support a)).height = (family (P.support anchor)).height := by
      apply AffineMap.ext_on
        ((isOpen_interior.inter isOpen_interior).affineSpan_eq_top ⟨c, interior_c, region_c⟩)
      intro z hz
      have cell_value := P.active a z (interior_subset hz.1)
      have region_value := (AffineEnvelope.mem_cell_iff _ _ _).mp (interior_subset hz.2).1
      exact cell_value.symm.trans region_value
    have same_side : signs a = signs anchor := by
      have lower := aligned a c (interior_subset interior_c)
      have lower_region : 0 ≤ AffineArrangement.signed f (signs anchor) c :=
        (interior_subset region_c).2
      have nonzero : AffineArrangement.signed f (signs anchor) c ≠ 0 := by
        intro zero
        exact not_mem_interior_of_affine_lower_bound _ signed_proper
          (fun _ hx => hx.2) zero region_c
      have strict := lt_of_le_of_ne lower_region nonzero.symm
      cases first : signs a <;> cases last : signs anchor <;>
        simp_all [AffineArrangement.signed] <;> linarith
    exact Set.mem_iUnion.mpr ⟨⟨a, height_eq, same_side⟩, member⟩
  apply Set.Subset.antisymm
  · intro x member
    have approached : x ∈ closure (interior (P.faceSideRegion anchor f signs)) := by
      rw [(P.convex_faceSideRegion anchor f signs).closure_interior_eq_closure_of_nonempty_interior
        full_region, (P.isClosed_faceSideRegion anchor f signs).closure_eq]
      exact member
    have closed_union :=
      isClosed_iUnion_of_finite (fun a : P.FaceSideIndex anchor signs => P.closed a.val)
    exact closed_union.closure_subset (closure_mono interior_covered approached)
  · exact Set.iUnion_subset (fun a => cell_subset a)

end Unfoldings.SpatialEnvelope.WholePartition
