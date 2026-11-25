module

public import Unfoldings.Polyhedron.SelectedComponentEuler
public import Unfoldings.Development.NetPartition

/-! The sum of individual cell counts is the total number of labeled components. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

open SpatialFolding.ConvexBoundary

universe u v w

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {L : Type w} (label : Face → L)

/-- The common label of the original faces of a labeled component. -/
def componentLabel : (C.labeledSeamGraph label).ConnectedComponent → L :=
  SimpleGraph.ConnectedComponent.lift label
    (fun _ _ walk _ => C.label_eq_of_labeledSeamGraph_reachable label ⟨walk⟩)

@[simp] theorem componentLabel_mk (f : Face) :
    C.componentLabel label ((C.labeledSeamGraph label).connectedComponentMk f) = label f := rfl

/-- Two selected faces are joined by the same seams whether we use the
entire label family or just the indicator of their cell. -/
theorem reachable_selectionLabel_iff (l : L) {f g : Face} (selected : label f = l) :
    (C.labeledSeamGraph (selectionLabel {x | label x = l})).Reachable f g ↔
      (C.labeledSeamGraph label).Reachable f g := by
  let U := {x | label x = l}
  let binary := C.labeledSeamGraph (selectionLabel U)
  let full := C.labeledSeamGraph label
  constructor
  · intro reachable
    rw [binary.reachable_iff_reflTransGen] at reachable
    apply (full.reachable_iff_reflTransGen _ _).mpr
    exact Relation.ReflTransGen.lift id (fun a b edge => by
      have compatible := (selectionLabel_eq_iff U edge.1).mp edge.2.1
      exact ⟨edge.1, compatible.1.trans compatible.2.symm, edge.2.2⟩) f g reachable
  · intro reachable
    apply (binary.reachable_iff_reflTransGen _ _).mpr
    have chain := (full.reachable_iff_reflTransGen _ _).mp reachable
    clear reachable
    induction chain with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b walk edge ih =>
      have first := (C.label_eq_of_labeledSeamGraph_reachable label
        ((full.reachable_iff_reflTransGen _ _).mpr walk)).symm.trans selected
      have last := edge.2.1.symm.trans first
      exact ih.tail ⟨edge.1, (selectionLabel_eq_iff U edge.1).mpr ⟨first, last⟩, edge.2.2⟩

/-- The selected components of one cell, allowing that cell to contain no original faces. -/
def SelectedComponents (U : Set Face) : Type u :=
  let G := C.labeledSeamGraph (selectionLabel U)
  {c : G.ConnectedComponent // ∃ f ∈ U, G.connectedComponentMk f = c}

private def selectionComponentsEquiv (l : L) :
    {c // C.componentLabel label c = l} ≃ C.SelectedComponents {x | label x = l} := by
  let U := {x | label x = l}
  let binary := C.labeledSeamGraph (selectionLabel U)
  let full := C.labeledSeamGraph label
  let rep (c : {c // C.componentLabel label c = l}) : Face := c.val.exists_rep.choose
  have repr (c : {c // C.componentLabel label c = l}) : full.connectedComponentMk (rep c) = c.val :=
    c.val.exists_rep.choose_spec
  have selected (c : {c // C.componentLabel label c = l}) : label (rep c) = l := by
    rw [← C.componentLabel_mk label, repr]
    exact c.property
  let map (c : {c // C.componentLabel label c = l}) : C.SelectedComponents U :=
    ⟨binary.connectedComponentMk (rep c), ⟨rep c, selected c, rfl⟩⟩
  apply Equiv.ofBijective map
  constructor
  · intro c d equal
    have same : binary.connectedComponentMk (rep c) = binary.connectedComponentMk (rep d) :=
      congrArg Subtype.val equal
    have reach := (C.reachable_selectionLabel_iff label l (selected c)).mp
      (SimpleGraph.ConnectedComponent.exact same)
    apply Subtype.ext
    exact (repr c).symm.trans ((SimpleGraph.ConnectedComponent.eq.mpr reach).trans (repr d))
  · rintro ⟨c, f, hf, equal⟩
    let d : {c // C.componentLabel label c = l} := ⟨full.connectedComponentMk f, hf⟩
    refine ⟨d, Subtype.ext ?_⟩
    have full_reach : full.Reachable (rep d) f :=
      SimpleGraph.ConnectedComponent.exact (repr d)
    have reach := (C.reachable_selectionLabel_iff label l (selected d)).mpr full_reach
    exact (SimpleGraph.ConnectedComponent.eq.mpr reach).trans equal

/-- A partition into labels counts exactly the sum of its separate selected components. -/
theorem card_labeledComponents_eq_sum_selectedComponents [Fintype L] :
    Nat.card (C.labeledSeamGraph label).ConnectedComponent =
      ∑ l, Nat.card (C.SelectedComponents {f | label f = l}) := by
  classical
  let e := (Equiv.sigmaFiberEquiv (C.componentLabel label)).symm
  have count := Nat.card_congr e
  rw [Nat.card_sigma] at count
  exact count.trans (Finset.sum_congr rfl (fun l _ => Nat.card_congr (C.selectionComponentsEquiv label l)))

end Unfoldings.TriangleComplex
