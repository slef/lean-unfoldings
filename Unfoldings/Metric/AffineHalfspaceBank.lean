module

public import Unfoldings.Metric.AffineHalfspaceCut
public import Unfoldings.Metric.ConvexCutSubfamily

/-! Canonical closed-halfspace banks inside an actual finitely partitioned flat cut plane. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]
  (cells : I → Set E) (closed : ∀ i, IsClosed (cells i))
  (convex : ∀ i, Convex ℝ (cells i)) (full : ∀ i, (interior (cells i)).Nonempty)
  (cover : (⋃ i, cells i) = Set.univ) (f : E →ᵃ[ℝ] ℝ) (proper : f ≠ 0)
  (signs : I → Bool)
  (aligned : ∀ i x, x ∈ cells i → 0 ≤ AffineArrangement.signed f (signs i) x)
  (side : Bool) (positive : ∃ q, 0 < AffineArrangement.signed f side q)
  (cuts : Set E) (cut_closed : IsClosed cuts) (cut_level : ∀ x ∈ cuts, f x = 0)

/-- The canonical actual bank maps the entire closed halfspace, including its cut boundary. -/
def affineHalfspaceBank : {x | 0 ≤ AffineArrangement.signed f side x} →
    PolygonalCut cells closed cuts :=
  cutSubfamilyMap cells closed cuts (fun i => signs i = side) ∘
    (affineHalfspaceCutIsometryEquiv cells closed f signs convex full cover proper aligned
      side positive cuts cut_closed cut_level).symm ∘ PolygonalPoint.ofSubtype

/-- The bank restores to precisely the original physical point. -/
theorem fold_affineHalfspaceBank (x : {x | 0 ≤ AffineArrangement.signed f side x}) :
    (cutSeams cells closed cuts).fold
      (affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
        cuts cut_closed cut_level x) = x.val := by
  let A := affineHalfspaceCutIsometryEquiv cells closed f signs convex full cover proper aligned
    side positive cuts cut_closed cut_level
  have positions (z : PolygonalCut (fun i : {i // signs i = side} => cells i.val)
      (fun i => closed i.val) cuts) :
      (A z).val = (cutSeams (fun i : {i // signs i = side} => cells i.val)
        (fun i => closed i.val) cuts).fold z := by
    obtain ⟨a, rfl⟩ := point_surjective (fun i : {i // signs i = side} => cells i.val)
      (cutSeams (fun i : {i // signs i = side} => cells i.val)
        (fun i => closed i.val) cuts).relation z
    rfl
  change (cutSeams cells closed cuts).fold
    (cutSubfamilyMap cells closed cuts (fun i => signs i = side)
      (A.symm (PolygonalPoint.ofSubtype x))) = _
  rw [fold_cutSubfamilyMap, ← positions, A.apply_symm_apply]
  rfl

/-- Bank points have exact ambient distances even in the full cut space. -/
theorem affineHalfspaceBank_isometry :
    Isometry (affineHalfspaceBank cells closed convex full cover f proper signs aligned
      side positive
      cuts cut_closed cut_level) := by
  let A := affineHalfspaceCutIsometryEquiv cells closed f signs convex full cover proper aligned
    side positive cuts cut_closed cut_level
  have halfspace_convex : Convex ℝ {x | 0 ≤ AffineArrangement.signed f side x} :=
    (convex_Ici (0 : ℝ)).affine_preimage (AffineArrangement.signed f side)
  have upper : LipschitzWith 1
      (affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
        cuts cut_closed cut_level) := by
    change LipschitzWith 1 (cutSubfamilyMap cells closed cuts (fun i => signs i = side) ∘
      A.symm ∘ PolygonalPoint.ofSubtype)
    simpa only [one_mul] using (cutSubfamilyMap_lipschitz cells closed cuts
      (fun i => signs i = side)).comp (A.symm.isometry.lipschitzWith.comp
        (convex_ofSubtype_isometry halfspace_convex).lipschitzWith)
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using upper x y
  · have bound := (cutSeams cells closed cuts).fold_lipschitz
      (affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
        cuts cut_closed cut_level x)
      (affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
        cuts cut_closed cut_level y)
    rw [fold_affineHalfspaceBank, fold_affineHalfspaceBank] at bound
    simpa only [Subtype.edist_eq, ENNReal.coe_one, one_mul] using bound

/-- Any original cell on this side gives exactly the canonical bank copy. -/
theorem affineHalfspaceBank_eq_of_mem (x : {x | 0 ≤ AffineArrangement.signed f side x})
    (i : {i // signs i = side}) (member : x.val ∈ cells i.val) :
    affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
      cuts cut_closed cut_level x =
        of (fun i => cells i) (cutSeams cells closed cuts).relation i.val ⟨x.val, member⟩ := by
  let A := affineHalfspaceCutIsometryEquiv cells closed f signs convex full cover proper aligned
    side positive cuts cut_closed cut_level
  have copy : A.symm (PolygonalPoint.ofSubtype x) =
      of (fun i : {i // signs i = side} => cells i.val)
        (cutSeams (fun i : {i // signs i = side} => cells i.val)
          (fun i => closed i.val) cuts).relation
        i ⟨x.val, member⟩ := by
    apply A.injective
    rw [A.apply_symm_apply]
    apply PolygonalPoint.ext
    rfl
  change cutSubfamilyMap cells closed cuts (fun i => signs i = side)
    (A.symm (PolygonalPoint.ofSubtype x)) = _
  rw [copy, cutSubfamilyMap_of]


/-- The canonical banks account for every actual metric point of the cut space. -/
theorem exists_affineHalfspaceBank_rep
    (positive : ∀ side : Bool, ∃ q, 0 < AffineArrangement.signed f side q)
    (z : PolygonalCut cells closed cuts) :
    ∃ side : Bool, ∃ x : {x | 0 ≤ AffineArrangement.signed f side x},
      affineHalfspaceBank cells closed convex full cover f proper signs aligned side
        (positive side) cuts cut_closed cut_level x = z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := point_surjective (fun i => cells i)
    (cutSeams cells closed cuts).relation z
  refine ⟨signs i, ⟨x.val, aligned i x.val x.property⟩, ?_⟩
  exact affineHalfspaceBank_eq_of_mem cells closed convex full cover f proper signs aligned
    (signs i) (positive (signs i)) cuts cut_closed cut_level _ ⟨i, rfl⟩ x.property

/-- Canonical copies from different sides agree wherever the physical point is uncut. -/
theorem affineHalfspaceBanks_eq_off_cuts
    (other : Bool) (other_positive : ∃ q, 0 < AffineArrangement.signed f other q)
    (x : {x | 0 ≤ AffineArrangement.signed f side x})
    (y : {x | 0 ≤ AffineArrangement.signed f other x}) (same : x.val = y.val)
    (outside : x.val ∉ cuts) :
    affineHalfspaceBank cells closed convex full cover f proper signs aligned side positive
      cuts cut_closed cut_level x =
    affineHalfspaceBank cells closed convex full cover f proper signs aligned other other_positive
      cuts cut_closed cut_level y := by
  have positions (z : PolygonalCut cells closed cuts) :
      (cutToPolygonal cells closed cuts convex cover.symm z).val =
        (cutSeams cells closed cuts).fold z := by
    obtain ⟨a, rfl⟩ := point_surjective (fun i => cells i) (cutSeams cells closed cuts).relation z
    rfl
  apply cutToPolygonal_injective_off_cuts cells closed cuts convex cover.symm
  · apply PolygonalPoint.ext
    rw [positions, positions, fold_affineHalfspaceBank, fold_affineHalfspaceBank]
    exact same
  · rw [positions, fold_affineHalfspaceBank]
    exact outside

end Unfoldings.MetricGluing
