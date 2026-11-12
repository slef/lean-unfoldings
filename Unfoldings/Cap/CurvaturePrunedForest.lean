module

public import Unfoldings.Cap.FlatSubtreeBanks
public import Unfoldings.Complex.SelectedCutRootSupport

/-! Remove every zero-curvature descendant subtree from the actual original cutting forest. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

open Classical in
def curvedParents : AscendingParents (C.Vertex Set.univ) where
  roots := M.parents.roots ∪ {v | M.subtreeCurvature v = 0}
  parent v := if v ∈ M.parents.roots ∪ {v | M.subtreeCurvature v = 0}
    then v else M.parents.parent v
  height := M.parents.height
  fixed_root v root := ite_eq_left root
  ascending v nonroot := by
    rw [ite_eq_right nonroot]
    exact M.parents.ascending v (fun root => nonroot (Or.inl root))

open Classical in
theorem curved_parent_eq (e : {v : C.Vertex Set.univ // v ∉ M.curvedParents.roots}) :
    M.curvedParents.parent e.val = M.parents.parent e.val :=
  ite_eq_right e.property

open Classical in
def curvedSelection : M.curvedParents.EdgeSelection C.seamGraph where
  edge e := M.selection.edge ⟨e.val, fun root => e.property (Or.inl root)⟩
  link e := by
    rw [M.curved_parent_eq e]
    exact M.selection.link ⟨e.val, fun root => e.property (Or.inl root)⟩

open Classical in
def curvedRetain : Set C.Seam := C.selectedRetain M.curvedSelection

open Classical in
theorem retain_subset_curvedRetain : M.retain ⊆ M.curvedRetain := by
  intro s kept selected
  obtain ⟨e, rfl⟩ := selected
  exact kept ⟨⟨e.val, fun root => e.property (Or.inl root)⟩, rfl⟩

open Classical in
theorem curvedRetain_subset_coherentSeams (D : FacewiseDevelopment C M.retain) :
    M.curvedRetain ⊆ D.coherentSeams := by
  intro s kept
  by_cases old : s ∈ M.retain
  · exact D.retain_subset_coherentSeams old
  · have selected : s ∈ Set.range M.selection.edge := Classical.not_not.mp old
    obtain ⟨e, rfl⟩ := selected
    apply M.parent_seam_coherent_of_flat D e
    by_contra nonflat
    let a : {v : C.Vertex Set.univ // v ∉ M.curvedParents.roots} :=
      ⟨e.val, fun root => root.elim e.property nonflat⟩
    exact kept ⟨a, rfl⟩

open Classical in
theorem curved_parent_root_original
    (e : {v : C.Vertex Set.univ // v ∉ M.curvedParents.roots})
    (root : M.curvedParents.parent e.val ∈ M.curvedParents.roots) :
    M.curvedParents.parent e.val ∈ M.parents.roots := by
  rw [M.curved_parent_eq e] at root ⊢
  rcases root with original | flat
  · exact original
  · have child_flat := M.subtreeCurvature_descendant_zero (M.parents.ancestor_parent e.val) flat
    exact (e.property (Or.inr child_flat)).elim

open Classical in
theorem curved_rootedForest :
    (C.relativeCutGraph M.curvedRetain Set.univ).IsRootedForest
      (C.relativeCutRoots Set.univ) := by
  apply C.selectedCut_rootedForest_of_root_support M.curvedSelection
  · intro v boundary
    exact Or.inl ((Set.ext_iff.mp M.roots_eq v).mpr boundary)
  · intro v root member
    rcases member with boundary | ⟨s, b, rfl⟩
    · exact boundary
    · have selected : s.val ∈ Set.range M.curvedSelection.edge := Classical.not_not.mp s.property.2
      obtain ⟨e, chosen⟩ := selected
      change C.seamVertex s.val b ∈ M.curvedParents.roots at root
      change C.IsBoundaryVertex Set.univ (C.seamVertex s.val b)
      rw [← chosen] at root ⊢
      have parent_boundary (parent_root : M.curvedParents.parent e.val ∈ M.curvedParents.roots) :
          C.IsBoundaryVertex Set.univ (M.curvedParents.parent e.val) :=
        (Set.ext_iff.mp M.roots_eq _).mp (M.curved_parent_root_original e parent_root)
      rcases M.curvedSelection.link e with ⟨first, last⟩ | ⟨first, last⟩
      · cases b
        · exact (e.property (first.symm ▸ root)).elim
        · exact last ▸ parent_boundary (last.symm ▸ root)
      · cases b
        · exact last ▸ parent_boundary (last.symm ▸ root)
        · exact (e.property (first.symm ▸ root)).elim

open Classical in
def curvedCutDisk : C.Realization M.curvedRetain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  K.folding.cutDiskHomeomorphOfRootedForest (Set.subset_univ _) K.diskHomeomorph
    M.curved_rootedForest

open Classical in
theorem curved_cut_subtree_positive {s : C.Seam} (cut : s ∉ M.curvedRetain) :
    ∃ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
      M.selection.edge e = s ∧ 0 < M.subtreeCurvature e.val := by
  have selected : s ∈ Set.range M.curvedSelection.edge := Classical.not_not.mp cut
  obtain ⟨e, rfl⟩ := selected
  refine ⟨⟨e.val, fun root => e.property (Or.inl root)⟩, rfl, ?_⟩
  exact lt_of_le_of_ne (M.subtreeCurvature_nonneg e.val)
    (fun zero => e.property (Or.inr zero.symm))

open Classical in
theorem curved_parent_cut_iff (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots}) :
    M.selection.edge e ∉ M.curvedRetain ↔ 0 < M.subtreeCurvature e.val := by
  constructor
  · intro cut
    obtain ⟨v, named, positive⟩ := M.curved_cut_subtree_positive cut
    have same : v = e := M.selection.edge_injective named
    exact same ▸ positive
  · intro positive kept
    let a : {v : C.Vertex Set.univ // v ∉ M.curvedParents.roots} :=
      ⟨e.val, fun root => root.elim e.property (ne_of_gt positive)⟩
    exact kept ⟨a, rfl⟩

open Classical in
def curvedDevelopment (D : FacewiseDevelopment C M.retain) (nonoverlap : D.Nonoverlapping) :
    FacewiseDevelopment C M.curvedRetain :=
  D.restoreSeams K.folding nonoverlap M.curvedRetain (M.curvedRetain_subset_coherentSeams D)

open Classical in
theorem curvedDevelopment_nonoverlapping (D : FacewiseDevelopment C M.retain)
    (nonoverlap : D.Nonoverlapping) : (M.curvedDevelopment D nonoverlap).Nonoverlapping :=
  nonoverlap

namespace SectorFrameData

variable {M}

open Classical in
theorem curved_parent_bank_interiors_ne {positive : 0 < t} {small : t < 1}
    {D : FacewiseDevelopment C M.retain} (B : M.SectorFrameData positive small D)
    (e : {v : C.Vertex Set.univ // v ∉ M.parents.roots})
    (cut : M.selection.edge e ∉ M.curvedRetain) {s r : ℝ}
    (s_before : s < 1) (r_before : r < 1)
    (budget : C.totalInteriorAngularDefect Set.univ < Real.pi) :
    M.parentEntrancePoint D e s ≠ M.parentExitPoint D e r :=
  B.parent_bank_interiors_ne e s_before r_before budget ((M.curved_parent_cut_iff e).mp cut)

end SectorFrameData

end Unfoldings.ConvexCap.SectorForest
