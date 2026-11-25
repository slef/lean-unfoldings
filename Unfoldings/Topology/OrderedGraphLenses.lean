module

public import Unfoldings.Topology.TwoGraphJordan
public import Mathlib.Data.Finset.Sort

/-! Enumerate the consecutive Jordan lenses of two graphs whose crossings are finite. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- The portion of the two graphs bounding one lens. -/
def graphLens (f g : ℝ → ℝ) (a b : ℝ) : Set Plane :=
  graphPoint f '' Set.Icc a b ∪ graphPoint g '' Set.Icc a b

/-- All intersections are accounted for in order. The associated Jordan disks
have disjoint interiors, and those interiors avoid both full graph traces. -/
theorem exists_ordered_graphLenses (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (ordered : a < b) (start : f a = g a) (finish : f b = g b)
    (finite : {t ∈ Set.Icc a b | f t = g t}.Finite) :
    ∃ (n : ℕ) (crossing : Fin (n + 2) ↪o ℝ),
      crossing 0 = a ∧ crossing (Fin.last (n + 1)) = b ∧
      Set.range crossing = {t ∈ Set.Icc a b | f t = g t} ∧
      (∀ i : Fin (n + 1), Schoenflies.IsJordanCurve
        (graphLens f g (crossing i.castSucc) (crossing i.succ))) ∧
      (Pairwise fun i j : Fin (n + 1) => Disjoint
        (interior (closedJordanDomain (graphLens f g (crossing i.castSucc) (crossing i.succ))))
        (interior (closedJordanDomain (graphLens f g (crossing j.castSucc) (crossing j.succ))))) ∧
      ∀ i : Fin (n + 1), Disjoint
        (interior (closedJordanDomain (graphLens f g (crossing i.castSucc) (crossing i.succ))))
        (Set.range (graphPoint f) ∪ Set.range (graphPoint g)) := by
  classical
  let S := finite.toFinset
  have at_a : a ∈ S := finite.mem_toFinset.mpr ⟨⟨le_rfl, ordered.le⟩, start⟩
  have at_b : b ∈ S := finite.mem_toFinset.mpr ⟨⟨ordered.le, le_rfl⟩, finish⟩
  have card : 2 ≤ S.card := by
    have included : ({a, b} : Finset ℝ) ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro at_a at_b
    simpa [ordered.ne] using Finset.card_le_card included
  let n := S.card - 2
  have count : S.card = n + 2 := by dsimp [n]; omega
  let crossing := S.orderEmbOfFin count
  have member (i : Fin (n + 2)) : crossing i ∈ Set.Icc a b ∧ f (crossing i) = g (crossing i) :=
    finite.mem_toFinset.mp (S.orderEmbOfFin_mem count i)
  have all_crossings : Set.range crossing = {t ∈ Set.Icc a b | f t = g t} :=
    (S.range_orderEmbOfFin count).trans finite.coe_toFinset
  have first : crossing 0 = a := by
    apply le_antisymm _ (member 0).1.1
    obtain ⟨i, equal⟩ := all_crossings.symm.subset (finite.mem_toFinset.mp at_a)
    rw [← equal]
    exact crossing.monotone (Fin.zero_le _)
  have last : crossing (Fin.last (n + 1)) = b := by
    apply le_antisymm (member _).1.2
    obtain ⟨i, equal⟩ := all_crossings.symm.subset (finite.mem_toFinset.mp at_b)
    rw [← equal]
    exact crossing.monotone (Fin.le_last _)
  have simple (i : Fin (n + 1)) : Schoenflies.IsJordanCurve
      (graphLens f g (crossing i.castSucc) (crossing i.succ)) := by
    apply isJordanCurve_two_graphs f g hf hg (crossing.strictMono (Fin.castSucc_lt_succ (i := i)))
      (member _).2 (member _).2
    intro t time agrees
    have in_range : t ∈ Set.range crossing := all_crossings.symm.subset
      ⟨⟨(member i.castSucc).1.1.trans time.1.le, time.2.le.trans (member i.succ).1.2⟩, agrees⟩
    obtain ⟨j, rfl⟩ := in_range
    have lower := crossing.lt_iff_lt.mp time.1
    have upper := crossing.lt_iff_lt.mp time.2
    change i.val < j.val at lower
    change j.val < i.val + 1 at upper
    omega
  refine ⟨n, crossing, first, last, all_crossings, simple, ?_, ?_⟩
  · intro i j different
    rcases lt_or_gt_of_ne different with before | after
    · exact disjoint_interior_two_graphs_of_le (simple i) (simple j)
        (crossing.monotone (show i.succ ≤ j.castSucc from before))
    · exact (disjoint_interior_two_graphs_of_le (simple j) (simple i)
        (crossing.monotone (show j.succ ≤ i.castSucc from after))).symm
  · intro i
    exact disjoint_interior_two_graphs_graphs (simple i)

end Unfoldings.PlanarTopology
