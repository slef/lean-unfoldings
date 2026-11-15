module

public import Unfoldings.Metric.CutCoverMap
public import Unfoldings.Metric.PhysicalCutCopyEquality

/-! Refining physical cut cells while retaining the exact metric within each original cell. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.MetricGluing

variable {E I J : Type*} [NormedAddCommGroup E] [Finite I] [Finite J]
  (coarse : I → Set E) (fine : J → Set E) (closed : ∀ j, IsClosed (fine j)) (cuts : Set E)

/-- A physical subdivision whose pieces in each original cell recover that cell's metric.
The per-cell metric follows, for example, from rigid planar boundary-cut isometries;
no global cut-metric equivalence or agreement along original seams is supplied. -/
structure PhysicalCutRefinement where
  parent : J → I
  included : ∀ j, fine j ⊆ coarse (parent j)
  cover : ∀ i, coarse i = ⋃ j : {j // parent j = i}, fine j.val
  fold_isometry : ∀ i, Isometry (cutSeams (fun j : {j // parent j = i} => fine j.val)
    (fun j => closed j.val) cuts).fold

namespace PhysicalCutRefinement

variable {coarse fine closed cuts} (R : PhysicalCutRefinement coarse fine closed cuts)

/-- Folding one complete refinement block into its specified original physical cell. -/
def parentFold (i : I)
    (x : PolygonalCut (fun j : {j // R.parent j = i} => fine j.val)
      (fun j => closed j.val) cuts) : coarse i :=
  ⟨(cutSeams (fun j : {j // R.parent j = i} => fine j.val) (fun j => closed j.val) cuts).fold x,
    by
      obtain ⟨⟨j, p⟩, rfl⟩ := point_surjective
        (fun j : {j // R.parent j = i} => fine j.val)
        (cutSeams (fun j : {j // R.parent j = i} => fine j.val)
          (fun j => closed j.val) cuts).relation x
      change p.val ∈ coarse i
      exact Eq.mp (congrArg (fun k => p.val ∈ coarse k) j.property)
        (R.included j.val p.property)⟩

omit [Finite I] in
theorem parentFold_isometry (i : I) : Isometry (R.parentFold i) := R.fold_isometry i

omit [Finite I] in
theorem parentFold_surjective (i : I) : Function.Surjective (R.parentFold i) := by
  intro x
  have covered : x.val ∈ ⋃ j : {j // R.parent j = i}, fine j.val :=
    Eq.mp (congrArg (fun s : Set E => x.val ∈ s) (R.cover i)) x.property
  obtain ⟨j, member⟩ := Set.mem_iUnion.mp covered
  exact ⟨of (fun j : {j // R.parent j = i} => fine j.val)
    (cutSeams (fun j : {j // R.parent j = i} => fine j.val) (fun j => closed j.val) cuts).relation
    j ⟨x.val, member⟩, Subtype.ext rfl⟩

/-- A whole original cell is exactly its actual subdivided cut block. -/
def parentFoldEquiv (i : I) :
    PolygonalCut (fun j : {j // R.parent j = i} => fine j.val) (fun j => closed j.val) cuts ≃ᵢ
      coarse i :=
  ⟨Equiv.ofBijective (R.parentFold i)
    ⟨(R.parentFold_isometry i).injective, R.parentFold_surjective i⟩, R.parentFold_isometry i⟩

/-- Include a complete original cell, reconstructed from its actual fine pieces. -/
def refinedCellMap (i : I) : coarse i → PolygonalCut fine closed cuts :=
  cutCoverMap (fun j : {j // R.parent j = i} => fine j.val) (fun j => closed j.val)
    fine closed Subtype.val (fun _ => Set.Subset.rfl) cuts ∘ (R.parentFoldEquiv i).symm

omit [Finite I] in
theorem refinedCellMap_lipschitz (i : I) : LipschitzWith 1 (R.refinedCellMap i) := by
  intro x y
  have bound := cutCoverMap_lipschitz (fun j : {j // R.parent j = i} => fine j.val)
    (fun j => closed j.val) fine closed Subtype.val (fun _ => Set.Subset.rfl) cuts
    ((R.parentFoldEquiv i).symm x) ((R.parentFoldEquiv i).symm y)
  exact bound.trans_eq (congrArg (fun d : ℝ≥0∞ => (1 : ℝ≥0∞) * d)
    ((R.parentFoldEquiv i).symm.isometry.edist_eq x y))

omit [Finite I] in
/-- Reconstructed original cells retain the original physical coordinates. -/
theorem fold_refinedCellMap (i : I) (x : coarse i) :
    (cutSeams fine closed cuts).fold (R.refinedCellMap i x) = x.val :=
  (fold_cutCoverMap (fun j : {j // R.parent j = i} => fine j.val)
    (fun j => closed j.val) fine closed Subtype.val (fun _ => Set.Subset.rfl) cuts _).trans
      (congrArg Subtype.val ((R.parentFoldEquiv i).apply_symm_apply x))

omit [Finite I] in
/-- Every specified fine-cell copy is unchanged by reconstruction of its original parent. -/
theorem refinedCellMap_of (j : J) (p : fine j) :
    R.refinedCellMap (R.parent j) ⟨p.val, R.included j p.property⟩ =
      of (fun j => fine j) (cutSeams fine closed cuts).relation j p := by
  let raw := of (fun k : {k // R.parent k = R.parent j} => fine k.val)
    (cutSeams (fun k : {k // R.parent k = R.parent j} => fine k.val)
      (fun k => closed k.val) cuts).relation ⟨j, rfl⟩ p
  have maps : R.parentFoldEquiv (R.parent j) raw = ⟨p.val, R.included j p.property⟩ :=
    Subtype.ext rfl
  have inverse : (R.parentFoldEquiv (R.parent j)).symm ⟨p.val, R.included j p.property⟩ = raw :=
    (R.parentFoldEquiv (R.parent j)).injective
      (((R.parentFoldEquiv (R.parent j)).apply_symm_apply _).trans maps.symm)
  exact congrArg (cutCoverMap (fun k : {k // R.parent k = R.parent j} => fine k.val)
    (fun k => closed k.val) fine closed Subtype.val (fun _ => Set.Subset.rfl) cuts) inverse

end PhysicalCutRefinement
end Unfoldings.MetricGluing
