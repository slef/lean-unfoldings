module

public import Mathlib.Topology.Connected.Clopen

/-! Compatible constant labels on a finite closed cover of a preconnected space agree. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem eq_of_finite_closed_cover {X I Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Finite I] (piece : I → Set X)
    (closed : ∀ i, IsClosed (piece i)) (cover : ⋃ i, piece i = Set.univ)
    (value : I → Y) (compatible : ∀ i j, (piece i ∩ piece j).Nonempty → value i = value j)
    {a b : I} (first : (piece a).Nonempty) (last : (piece b).Nonempty) :
    value a = value b := by
  classical
  let good : Set X := ⋃ i : {i // value i = value a}, piece i.val
  let bad : Set X := ⋃ i : {i // value i ≠ value a}, piece i.val
  have closed_good : IsClosed good := isClosed_iUnion_of_finite (fun i => closed i.val)
  have closed_bad : IsClosed bad := isClosed_iUnion_of_finite (fun i => closed i.val)
  have complement : goodᶜ = bad := by
    ext x
    constructor
    · intro absent
      obtain ⟨i, member⟩ := Set.mem_iUnion.mp (cover.symm ▸ Set.mem_univ x)
      have different : value i ≠ value a := fun same =>
        absent (Set.mem_iUnion.mpr ⟨⟨i, same⟩, member⟩)
      exact Set.mem_iUnion.mpr ⟨⟨i, different⟩, member⟩
    · intro member present
      obtain ⟨i, member_i⟩ := Set.mem_iUnion.mp member
      obtain ⟨j, member_j⟩ := Set.mem_iUnion.mp present
      exact i.property ((compatible i.val j.val ⟨x, member_i, member_j⟩).trans j.property)
  have nonempty_good : good.Nonempty := by
    obtain ⟨x, member⟩ := first
    exact ⟨x, Set.mem_iUnion.mpr ⟨⟨a, rfl⟩, member⟩⟩
  have open_good : IsOpen good := by
    rw [← isClosed_compl_iff, complement]
    exact closed_bad
  have all_good : good = Set.univ := IsClopen.eq_univ ⟨closed_good, open_good⟩ nonempty_good
  obtain ⟨x, member_b⟩ := last
  obtain ⟨i, member_i⟩ := Set.mem_iUnion.mp (all_good.symm ▸ Set.mem_univ x)
  exact i.property.symm.trans (compatible i.val b ⟨x, member_i, member_b⟩)

end Unfoldings
