module

public import Unfoldings.Geometry.CanonicalAncestorOpenings
public import Unfoldings.Geometry.OpeningPermutation

/-! A singleton original-source step gives the exact complete canonical bank update. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

open PolygonalChain

variable {V : Type*} [Fintype V] (P : AscendingParents V) (seeds : List V)
  (root : {v // v ∈ P.roots}) {n : ℕ} (path : Fin (n + 1) → V)
  (last : path (Fin.last n) = root.val) (weight : V → ℝ)

/-- The actual terminal phase is the processed original curvature in the rooted component. -/
theorem historyOpenings_tailHeading :
    openingTailHeading (P.historyOpenings seeds root path last weight) =
      ((P.initialFrontier).run seeds).processedDescendantWeight weight root.val := by
  classical
  unfold historyOpenings
  rw [withoutZeroOpenings_tailHeading, P.ancestorOpenings_tailHeading]
  have named : (P.historySources seeds root).toFinset =
      ((P.initialFrontier).run seeds).processedDescendants root.val := by
    ext source
    simp only [List.mem_toFinset, P.mem_historySources seeds root]
  calc
    _ = ∑ source ∈ (P.historySources seeds root).toFinset, weight source :=
      (List.sum_toFinset _ (P.historySources_nodup seeds root)).symm
    _ = _ := by rw [named]; rfl

variable (ordered : ∀ i j, i ≤ j → P.Ancestor (path i) (path j))
  (source : V) (fresh : source ∉ ((P.initialFrontier).run seeds).processed)
  (single : ((P.initialFrontier).run seeds).contactTime source = 1)
  (at_start : P.Ancestor source (path 0))

include ordered fresh single at_start

/-- No old charge is reassigned: the fresh source adds its original weight on every later bank. -/
theorem historyOpenings_source_heading (i : Fin n) :
    openingHeading (P.historyOpenings (seeds ++ [source]) root path last weight) i =
      openingHeading (P.historyOpenings seeds root path last weight) i + weight source := by
  rw [P.historyOpenings_heading _ _ _ _ _ ordered,
    P.historyOpenings_heading _ _ _ _ _ ordered]
  have update : (P.initialFrontier).run (seeds ++ [source]) =
      ((P.initialFrontier).run seeds).process source := by
    simp only [ParentFrontier.run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [update, ParentFrontier.processedDescendantWeight_single_step _ _ _ _ fresh single]
  have ancestor := at_start.trans P (ordered 0 i.castSucc (Fin.zero_le _))
  rw [ite_eq_left ancestor]

/-- The same original source charge is added once to the complete unbounded tail. -/
theorem historyOpenings_source_tailHeading :
    openingTailHeading (P.historyOpenings (seeds ++ [source]) root path last weight) =
      openingTailHeading (P.historyOpenings seeds root path last weight) + weight source := by
  rw [P.historyOpenings_tailHeading, P.historyOpenings_tailHeading]
  have update : (P.initialFrontier).run (seeds ++ [source]) =
      ((P.initialFrontier).run seeds).process source := by
    simp only [ParentFrontier.run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [update, ParentFrontier.processedDescendantWeight_single_step _ _ _ _ fresh single]
  have ancestor : P.Ancestor source root.val := by
    rw [← last]
    exact at_start.trans P (ordered 0 (Fin.last n) (Fin.zero_le _))
  rw [ite_eq_left ancestor]

/-- The complete canonical bank after processing is exactly its fresh source opening followed by
its old original history. This retains all hinge translations and the entire infinite tail. -/
theorem historyOpenings_source_bank (bank : PolygonalRay ℂ n) :
    bank.openings (P.historyOpenings (seeds ++ [source]) root path last weight) =
      bank.openings (⟨0, weight source⟩ :: P.historyOpenings seeds root path last weight) := by
  apply bank.openings_eq_of_heading_tail_eq
  · intro i
    rw [P.historyOpenings_source_heading seeds root path last weight ordered source fresh single
      at_start i]
    simp only [openingHeading, List.map_cons, List.sum_cons, Fin.zero_le, ite_true, add_comm]
  · rw [P.historyOpenings_source_tailHeading seeds root path last weight ordered source fresh single
      at_start]
    simp only [openingTailHeading, List.map_cons, List.sum_cons, add_comm]

end Unfoldings.AscendingParents
