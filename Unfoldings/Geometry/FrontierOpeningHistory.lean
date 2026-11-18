module

public import Unfoldings.Geometry.AncestorOpeningHistory
public import Unfoldings.Topology.ProcessedDescendantWeights

/-! Canonical original-source openings recover the actual processed descendant phases exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents.ParentFrontier

open PolygonalChain

variable {V : Type*} [Fintype V] {P : AscendingParents V} (S : P.ParentFrontier)
  {n : ℕ} (path : Fin (n + 1) → V) (weight : V → ℝ) (sources : List V)
  (reaches : ∀ source ∈ sources, ∃ i, P.Ancestor source (path i))

open Classical in
/-- On every original path bank, canonical source openings have the exact current subtree phase. -/
theorem ancestorOpenings_heading_eq_processedWeight
    (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j)) (distinct : sources.Nodup)
    (members : ∀ source, source ∈ sources ↔ source ∈ S.processedDescendants (path (Fin.last n)))
    (i : Fin n) :
    openingHeading (P.ancestorOpenings path weight sources reaches) i =
      S.processedDescendantWeight weight (path i.castSucc) := by
  classical
  have filtered : sources.toFinset.filter (fun source => P.Ancestor source (path i.castSucc)) =
      S.processedDescendants (path i.castSucc) := by
    ext source
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨present, ancestor⟩
      have old := (S.mem_processedDescendants _ _).mp ((members source).mp present)
      exact (S.mem_processedDescendants _ _).mpr ⟨old.1, ancestor⟩
    · intro present
      have old := (S.mem_processedDescendants _ _).mp present
      have last : P.Ancestor source (path (Fin.last n)) :=
        old.2.trans P (ordered _ _ (Fin.le_last _))
      exact ⟨(members source).mpr ((S.mem_processedDescendants _ _).mpr ⟨old.1, last⟩), old.2⟩
  rw [P.ancestorOpenings_heading path weight sources reaches ordered i]
  calc
    _ = ∑ source ∈ sources.toFinset,
        if P.Ancestor source (path i.castSucc) then weight source else 0 :=
      (List.sum_toFinset _ distinct).symm
    _ = ∑ source ∈ sources.toFinset.filter
        (fun source => P.Ancestor source (path i.castSucc)), weight source :=
      (Finset.sum_filter _ _).symm
    _ = S.processedDescendantWeight weight (path i.castSucc) := by
      rw [filtered]
      rfl

end Unfoldings.AscendingParents.ParentFrontier
