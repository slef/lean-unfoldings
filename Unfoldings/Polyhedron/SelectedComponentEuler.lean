module

public import Unfoldings.Polyhedron.LabeledComponentCount
public import Unfoldings.Combinatorics.SelectedComponentCount

/-! Euler accounting for the components selected by a single cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

open Classical in
/-- Selected faces have one common label. Each other face has its own label. -/
def selectionLabel (U : Set Face) (f : Face) : Option Face :=
  if f ∈ U then none else some f

theorem selectionLabel_eq_iff (U : Set Face) {f g : Face} (different : f ≠ g) :
    selectionLabel U f = selectionLabel U g ↔ f ∈ U ∧ g ∈ U := by
  classical
  by_cases hf : f ∈ U <;> by_cases hg : g ∈ U <;> simp [selectionLabel, hf, hg, different]

/-- A full original vertex link has every incident seam joining two selected faces. -/
def fullSelectedLink (U : Set Face) (v : C.Vertex Set.univ) : Prop :=
  ∀ s ∈ incidentSeams v, (C.left s).face ∈ U ∧ (C.right s).face ∈ U

open Classical in
include P in
/-- The number of selected components equals selected face count minus the
retained seam count plus the number of fully selected links. Only the actual
disk condition on the labeled components is needed. -/
theorem selected_components_eq_euler (U : Set Face)
    (disks : ∀ c : (C.labeledSeamGraph (selectionLabel U)).ConnectedComponent,
      C.RestrictionIsDisk c.supp) :
    let graph := C.labeledSeamGraph (selectionLabel U)
    let selectedComponent (c : graph.ConnectedComponent) :=
      ∃ f ∈ U, graph.connectedComponentMk f = c
    (Nat.card {c // selectedComponent c} : ℤ) =
      ((Finset.univ.filter (· ∈ U)).card : ℤ) -
        (Finset.univ.filter fun s : C.Seam => (C.left s).face ∈ U ∧ (C.right s).face ∈ U).card +
        ((Finset.univ : Finset (C.Vertex Set.univ)).filter (fullSelectedLink U)).card := by
  let label := selectionLabel U
  let graph := C.labeledSeamGraph label
  let keep (s : C.Seam) := (C.left s).face ∈ U ∧ (C.right s).face ∈ U
  let cut (s : C.Seam) := label (C.left s).face ≠ label (C.right s).face
  have kept (s : C.Seam) : s ∈ retainLabelSeams label ↔ keep s :=
    selectionLabel_eq_iff U (F.incident_faces_ne s)
  have internal {f g : Face} (h : graph.Adj f g) : f ∈ U :=
    ((selectionLabel_eq_iff U h.1).mp h.2.1).1
  have decomposition := card_components_eq_selected_add_card_isolated graph (· ∈ U) internal
  have cut_eq : cut = fun s => ¬ keep s := by
    funext s
    exact propext (not_congr (kept s))
  have inactive_eq : (fun v : C.Vertex Set.univ => ¬ labelCutVertex label v) = fullSelectedLink U := by
    funext v
    apply propext
    constructor
    · intro absent s incident
      by_contra missing
      have cut : s ∉ retainLabelSeams label := fun held => missing ((kept s).mp held)
      rcases (Finset.mem_filter.mp incident).2 with first | last
      · exact absent ⟨s, false, cut, first⟩
      · exact absent ⟨s, true, cut, last⟩
    · intro all
      rintro ⟨s, b, cut, endpoint⟩
      apply cut
      apply (kept s).mpr
      apply all s
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      cases b
      · exact Or.inl endpoint
      · exact Or.inr endpoint
  let inactive (v : C.Vertex Set.univ) := ¬ labelCutVertex label v
  have counts := P.labeled_components_eq_cut_cycle_rank label
  rw [P.card_labelCutGraph_components_of_disks label disks, Fintype.card_subtype] at counts
  have cuts_eq :
      (Finset.univ.filter fun s : C.Seam => label (C.left s).face ≠ label (C.right s).face) =
        Finset.univ.filter (fun s => ¬ keep s) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.of_eq (congrFun cut_eq s)
  have inactive_card : Nat.card {v // inactive v} =
      ((Finset.univ : Finset (C.Vertex Set.univ)).filter (fullSelectedLink U)).card := by
    rw [Nat.card_eq_fintype_card (α := {v // inactive v}), Fintype.card_subtype]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.of_eq (congrFun inactive_eq v)
  change _ + _ = 1 +
    (Finset.univ.filter fun s : C.Seam => label (C.left s).face ≠ label (C.right s).face).card +
      (1 + Nat.card {v // inactive v}) at counts
  rw [decomposition, cuts_eq, inactive_card] at counts
  have face_sum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Face)) (· ∈ U)
  have seam_sum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset C.Seam)) keep
  rw [Finset.card_univ] at face_sum seam_sum
  have outside : Nat.card {f : Face // f ∉ U} = (Finset.univ.filter (· ∉ U)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [outside] at counts
  have euler := P.triangulation_euler
  dsimp only
  change (Nat.card {c : graph.ConnectedComponent // ∃ f ∈ U, graph.connectedComponentMk f = c} :
      ℤ) = _ - ((Finset.univ.filter keep).card : ℤ) + _
  omega

end Unfoldings.SpatialFolding.ConvexBoundary
