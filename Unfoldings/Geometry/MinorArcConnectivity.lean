module

public import Unfoldings.Geometry.MinorArcCrofton

/-! Closed minor arcs are continuous images of their chord intervals. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The minor arc together with both endpoints. -/
def closedMinorArc (u v : Space) : Set Space :=
  insert u (insert v (openMinorArc u v))

theorem isPreconnected_closedMinorArc {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) : IsPreconnected (closedMinorArc u v) := by
  let chord (t : ℝ) := (1 - t) • u + t • v
  let ray (t : ℝ) := NormedSpace.normalize (chord t)
  have first : ray 0 = u := by
    simpa [ray, chord] using NormedSpace.normalize_eq_self_of_norm_eq_one hu
  have last : ray 1 = v := by
    simpa [ray, chord] using NormedSpace.normalize_eq_self_of_norm_eq_one hv
  have positive (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ‖chord t‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    rcases eq_or_lt_of_le ht.1 with equal | greater
    · subst t
      simp [chord, norm_ne_zero_iff.mp (by rw [hu]; norm_num)]
    · rcases eq_or_lt_of_le ht.2 with equal | less
      · subst t
        simp [chord, norm_ne_zero_iff.mp (by rw [hv]; norm_num)]
      · exact minorArc_chord_ne_zero hu hv not_antipodal ⟨greater, less⟩
  have hc : Continuous chord := by dsimp [chord]; fun_prop
  have hr : ContinuousOn ray (Set.Icc 0 1) :=
    (hc.continuousOn.norm.inv₀ positive).smul hc.continuousOn
  have exact : ray '' Set.Icc 0 1 = closedMinorArc u v := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases eq_or_lt_of_le ht.1 with equal | greater
      · subst t
        rw [first]
        exact Set.mem_insert _ _
      · rcases eq_or_lt_of_le ht.2 with equal | less
        · subst t
          rw [last]
          exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
            (show ray t ∈ openMinorArc u v from ⟨t, ⟨greater, less⟩, rfl⟩))
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨0, by norm_num, first⟩
      · rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact ⟨1, by norm_num, last⟩
        · obtain ⟨t, ht, rfl⟩ := hx
          exact ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
  rw [← exact]
  exact (convex_Icc (0 : ℝ) 1).isPreconnected.image ray hr

/-- Two endpoints in different disjoint open cells force an interior hit
on the network if the cells and network cover the whole closed minor arc. -/
theorem exists_openMinorArc_mem_network_of_separate {I : Type*} (cell : I → Set Space)
    (op : ∀ i, IsOpen (cell i)) (disjoint : Pairwise (fun i j => Disjoint (cell i) (cell j)))
    {network : Set Space} {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (not_antipodal : u + v ≠ 0) {i j : I} (diff : i ≠ j)
    (left : u ∈ cell i) (right : v ∈ cell j)
    (coverage : closedMinorArc u v ⊆ (⋃ i, cell i) ∪ network) :
    ∃ x ∈ openMinorArc u v, x ∈ network := by
  by_contra no_hit
  let others := ⋃ k : {k : I // k ≠ i}, cell k
  have apart : Disjoint (cell i) others := by
    refine Set.disjoint_iUnion_right.mpr fun k => ?_
    exact disjoint k.property.symm
  have cover : closedMinorArc u v ⊆ cell i ∪ others := by
    intro x hx
    have internal : x ∈ ⋃ k, cell k := by
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact Set.mem_iUnion.mpr ⟨i, left⟩
      · rcases Set.mem_insert_iff.mp hx' with rfl | hx'
        · exact Set.mem_iUnion.mpr ⟨j, right⟩
        · exact (coverage hx).resolve_right fun hit => no_hit ⟨x, hx', hit⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp internal
    by_cases same : k = i
    · exact Or.inl (same ▸ hk)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, same⟩, hk⟩)
  have other_open : IsOpen others := isOpen_iUnion (fun k : {k : I // k ≠ i} => op k)
  have subset := (isPreconnected_closedMinorArc hu hv not_antipodal).subset_left_of_subset_union
    (op i) other_open apart cover ⟨u, Set.mem_insert _ _, left⟩
  exact Set.disjoint_left.mp (disjoint diff)
    (subset (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) right

end Unfoldings
