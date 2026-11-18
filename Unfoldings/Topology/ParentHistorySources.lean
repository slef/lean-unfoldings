module

public import Unfoldings.Topology.ParentFrontierReach
public import Unfoldings.Topology.ProcessedDescendantIncidence

/-! First-contact history gives distinct, ordered original charges in each rooted component. -/

@[expose] public section

noncomputable section

namespace Unfoldings.AscendingParents

variable {V : Type*} [Fintype V] (P : AscendingParents V) (seeds : List V)
  (root : {v // v ∈ P.roots})

open Classical in
/-- Keep the first-contact source order within a component. Its original root is included once. -/
def historySources : List V :=
  root.val :: (((P.initialFrontier).history seeds).map Subtype.val).filter
    (fun source => decide (P.Ancestor source root.val))

/-- No original charge is duplicated; the root and all nonroot source labels stay distinct. -/
theorem historySources_nodup : (P.historySources seeds root).Nodup := by
  classical
  have original : (((P.initialFrontier).history seeds).map Subtype.val).Nodup :=
    ((P.initialFrontier).history_nodup seeds).map (fun _ _ same => Subtype.ext same)
  apply List.nodup_cons.mpr
  constructor
  · intro present
    obtain ⟨source, _, same⟩ := List.mem_map.mp (List.mem_filter.mp present).1
    exact source.property (same.symm ▸ root.property)
  · exact original.filter _

/-- The component's charge list is exactly its actual current processed original descendants. -/
theorem mem_historySources (source : V) :
    source ∈ P.historySources seeds root ↔
      source ∈ ((P.initialFrontier).run seeds).processedDescendants root.val := by
  classical
  rw [historySources, List.mem_cons, List.mem_filter]
  constructor
  · rintro (same | ⟨present, ancestor⟩)
    · subst source
      exact (ParentFrontier.mem_processedDescendants _ _ _).mpr
        ⟨((P.initialFrontier).run seeds).roots root.property, P.ancestor_refl _⟩
    · obtain ⟨named, member, rfl⟩ := List.mem_map.mp present
      have reached := ((P.initialFrontier).mem_history_iff seeds named).mp member
      exact (ParentFrontier.mem_processedDescendants _ _ _).mpr
        ⟨((P.initialFrontier).mem_run_iff seeds _).mpr (Or.inr reached.2),
          of_decide_eq_true ancestor⟩
  · intro present
    have current := (ParentFrontier.mem_processedDescendants _ _ _).mp present
    by_cases isroot : source ∈ P.roots
    · exact Or.inl (P.ancestor_root_unique (P.ancestor_refl source) current.2 isroot root.property)
    · apply Or.inr
      have named : (⟨source, isroot⟩ : {v // v ∉ P.roots}) ∈
          (P.initialFrontier).history seeds := by
        apply ((P.initialFrontier).mem_history_iff seeds _).mpr
        have reached := ((P.initialFrontier).mem_run_iff seeds source).mp current.1
        exact ⟨isroot, reached.resolve_left isroot⟩
      exact ⟨List.mem_map.mpr ⟨⟨source, isroot⟩, named, rfl⟩, decide_eq_true current.2⟩

/-- Every retained original charge reaches the component's named actual root. -/
theorem historySources_ancestor (source : V) (member : source ∈ P.historySources seeds root) :
    P.Ancestor source root.val :=
  ((ParentFrontier.mem_processedDescendants _ _ _).mp
    ((P.mem_historySources seeds root source).mp member)).2

end Unfoldings.AscendingParents
