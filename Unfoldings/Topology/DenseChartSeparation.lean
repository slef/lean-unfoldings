module

public import Mathlib.Topology.Homeomorph.Lemmas

/-! Injectivity on an open dense set separates actual open chart images. -/

@[expose] public section

namespace Unfoldings

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Overlap of open chart images cannot hide in the omitted nowhere-dense set. -/
theorem disjoint_homeomorph_images_of_dense_injective
    (first last : X ≃ₜ Y) {F : X → Y} {A U V : Set X}
    (opened : IsOpen A) (dense : Dense A) (first_open : IsOpen U) (last_open : IsOpen V)
    (separate : Disjoint U V) (first_agrees : Set.EqOn F first U)
    (last_agrees : Set.EqOn F last V) (injective : Set.InjOn F (A ∩ (U ∪ V))) :
    Disjoint (first '' U) (last '' V) := by
  have first_dense := first.surjective.denseRange.dense_image first.continuous dense
  have last_dense := last.surjective.denseRange.dense_image last.continuous dense
  have both := first_dense.inter_of_isOpen_left last_dense (first.isOpenMap A opened)
  apply Set.disjoint_left.mpr
  intro p first_member last_member
  obtain ⟨q, ⟨⟨a, a_regular, at_a⟩, ⟨b, b_regular, at_b⟩⟩,
    ⟨⟨x, x_member, at_x⟩, ⟨y, y_member, at_y⟩⟩⟩ := both.exists_mem_open
      ((first.isOpenMap U first_open).inter (last.isOpenMap V last_open))
      ⟨p, first_member, last_member⟩
  have a_member : a ∈ U := first.injective (at_a.trans at_x.symm) ▸ x_member
  have b_member : b ∈ V := last.injective (at_b.trans at_y.symm) ▸ y_member
  have equal : F a = F b := (first_agrees a_member).trans
    ((at_a.trans at_b.symm).trans (last_agrees b_member).symm)
  have same := injective ⟨a_regular, Or.inl a_member⟩ ⟨b_regular, Or.inr b_member⟩ equal
  exact Set.disjoint_left.mp separate a_member (same.symm ▸ b_member)

end Unfoldings
