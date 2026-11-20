module

public import Unfoldings.Development.FaceRestriction
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Surface partitions into connected nonoverlapping nets along original edges. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v w

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
/-- A whole-face piece has a one-piece original-edge net when retaining some of
its original seams gives a disk with a nonoverlapping rigid development. -/
def HasOriginalEdgeNet (U : Set Face) : Prop :=
  ∃ retain : Set (C.restrictFaces U).Seam,
    Nonempty ((C.restrictFaces U).Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
    ∃ D : FacewiseDevelopment (C.restrictFaces U) retain, D.Nonoverlapping

/-- Every input face has exactly one label and every label is used.
Different pieces have independent planar placements. -/
def HasNetPartition (n : ℕ) : Prop :=
  ∃ piece : Face → Fin n, Function.Surjective piece ∧
    ∀ i, C.HasOriginalEdgeNet (piece ⁻¹' {i})

/-- The edges of this graph are precisely the original seams joining faces of the same label. -/
def labeledSeamGraph {Label : Type w} (label : Face → Label) : SimpleGraph Face where
  Adj f g := f ≠ g ∧ label f = label g ∧ ∃ s : C.Seam,
    ((C.left s).face = f ∧ (C.right s).face = g) ∨
      ((C.left s).face = g ∧ (C.right s).face = f)
  symm := by
    constructor
    intro f g h
    obtain ⟨different, same, s, pair⟩ := h
    exact ⟨different.symm, same.symm, s, pair.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A connected component of equal-label seams has a single original label. -/
theorem label_eq_of_labeledSeamGraph_reachable {Label : Type w} (label : Face → Label)
    {f g : Face} (reach : (C.labeledSeamGraph label).Reachable f g) : label f = label g := by
  have chain := ((C.labeledSeamGraph label).reachable_iff_reflTransGen f g).mp reach
  clear reach
  induction chain with
  | refl => rfl
  | tail _ edge ih => exact ih.trans edge.2.1

open Classical in
/-- The component count is exactly the number of pieces in the assembled
partition. The labeling uses the input face type throughout. -/
theorem hasNetPartition_card_labeledSeamGraph {Label : Type w} (label : Face → Label)
    (nets : ∀ c : (C.labeledSeamGraph label).ConnectedComponent, C.HasOriginalEdgeNet c.supp) :
    C.HasNetPartition (Nat.card (C.labeledSeamGraph label).ConnectedComponent) := by
  let G := C.labeledSeamGraph label
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let index : G.ConnectedComponent ≃ Fin (Nat.card G.ConnectedComponent) :=
    (Fintype.equivFin G.ConnectedComponent).trans
      (finCongr (Nat.card_eq_fintype_card (α := G.ConnectedComponent)).symm)
  let piece := index ∘ G.connectedComponentMk
  have onto : Function.Surjective G.connectedComponentMk := by
    intro c
    exact c.exists_rep
  refine ⟨piece, index.surjective.comp onto, ?_⟩
  intro i
  have fiber : piece ⁻¹' {i} = (index.symm i).supp := by
    ext f
    change index (G.connectedComponentMk f) = i ↔ G.connectedComponentMk f = index.symm i
    exact ⟨fun h => index.injective (h.trans (index.apply_symm_apply i).symm),
      fun h => (congrArg index h).trans (index.apply_symm_apply i)⟩
  rw [fiber]
  exact nets (index.symm i)

end Unfoldings.TriangleComplex
