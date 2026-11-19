module

public import Unfoldings.Metric.Barrier

/-! Conserved labels with finite fibers rule out infinite seam classes. -/

@[expose] public section

namespace Unfoldings.MetricGluing

variable {I L : Type*} {E : I → Type*}
  (glue : Total E → Total E → Prop) (label : Total E → L)
  (compatible : ∀ a b, glue a b → label a = label b)

include compatible

/-- Every actual finite chain of seam identifications preserves its original label. -/
theorem label_eq_of_eqvGen {a b : Total E} (related : Relation.EqvGen glue a b) :
    label a = label b := by
  induction related with
  | rel a b seam => exact compatible a b seam
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first last => exact first.trans last

/-- Each seam class is finite in each cell when its conserved labels have finite fibers.
The labels need not be injective, continuous or a planar development. -/
theorem finite_classIn_of_finite_label_fibers
    (finite : ∀ i l, {p : E i | label ⟨i, p⟩ = l}.Finite)
    (a : Total E) (i : I) : (classIn E glue a i).Finite :=
  (finite i (label a)).subset (fun _ related =>
    (label_eq_of_eqvGen glue label compatible related).symm)

end Unfoldings.MetricGluing
