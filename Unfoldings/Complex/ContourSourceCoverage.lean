module

public import Unfoldings.Complex.ContourFirstVisit
public import Unfoldings.Complex.IntrinsicBoundary

/-! The wrap of a rim-anchored contour contains no omitted positive source. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))

local notation "Retain" => C.selectedRetain S
local notation "Forget" => C.vertexForgetCuts (Set.subset_univ Retain)
local notation "Visit[" q "," j "]" => C.contourOriginalVertex S q j

include Q in
/-- Rotating past an original rim bank puts a root on both sides of the wrap. -/
theorem exists_contour_starts_ends_root (p : C.BoundaryEnd Set.univ)
    (roots : C.relativeCutRoots Set.univ ⊆ P.roots) :
    ∃ A : C.BoundaryContour Retain, Visit[A,0] ∈ P.roots ∧
      Visit[A,Fin.last A.length] ∈ P.roots := by
  let old : C.BoundaryEnd Retain := ⟨p.val, C.isBoundaryEdge_antitone (Set.subset_univ _) p.property⟩
  obtain ⟨i, h⟩ := Q.covers old
  have bank : ((C.boundaryEndEquiv Retain old).1) =
      ((C.boundaryEndEquiv Retain (Q.cycle.point i)).1) :=
    (C.boundaryEnd_bank_eq_iff Retain _ _).mpr h
  have original_edge : C.germEdge (Q.cycle.point i).val = C.germEdge p.val :=
    (congrArg Subtype.val bank).symm
  have turn_edge : C.germEdge (C.boundaryTurn Retain (Q.cycle.point i)).val = C.germEdge p.val :=
    (congrArg Subtype.val ((C.boundaryEnd_bank_eq_iff Retain _ _).mpr (Or.inr rfl))).trans
      original_edge
  have root (g : C.BoundaryEnd Retain) (edge : C.germEdge g.val = C.germEdge p.val) :
      Forget (C.boundaryEndVertex Retain g) ∈ P.roots := by
    let original : C.BoundaryEnd Set.univ := ⟨g.val, edge.symm ▸ p.property⟩
    exact roots (C.boundaryEndAsVertex Set.univ original).property
  let first := finRotate (Q.length + 1) i
  let A := Q.rotate C first
  have before : Fin.last Q.length + first = i := by
    change Fin.last Q.length + finRotate (Q.length + 1) i = i
    rw [finRotate_apply]
    have wrap : (Fin.last Q.length : Fin (Q.length + 1)) + 1 = 0 := by
      rw [← finRotate_apply, finRotate_last]
    calc
      _ = i + (Fin.last Q.length + 1) := by abel
      _ = i := by rw [wrap, add_zero]
  let physical (g : C.BoundaryEnd Retain) := Forget (C.boundaryEndVertex Retain g)
  have first_copy : physical (A.cycle.point 0) =
      physical (C.boundaryTurn Retain (Q.cycle.point i)) :=
    (congrArg physical ((Q.rotate_first C first).trans (Q.next_cyclic C i).symm)).trans
      (congrArg Forget ((C.boundaryMate_spec Retain _).2))
  have last_copy : physical (A.cycle.point (Fin.last A.length)) = physical (Q.cycle.point i) :=
    congrArg physical ((Q.rotate_point C first (Fin.last Q.length)).trans
      (congrArg Q.cycle.point before))
  refine ⟨A, ?_, ?_⟩
  · change physical (A.cycle.point 0) ∈ P.roots
    rw [first_copy]
    exact root _ turn_edge
  · change physical (A.cycle.point (Fin.last A.length)) ∈ P.roots
    rw [last_copy]
    exact root _ original_edge

include Q in
/-- An original intrinsic disk supplies a rim bank on which to anchor the contour. -/
theorem exists_contour_starts_ends_root_of_disk (F : SpatialFolding C)
    (disk : C.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1)
    (roots : C.relativeCutRoots Set.univ ⊆ P.roots) :
    ∃ A : C.BoundaryContour Retain, Visit[A,0] ∈ P.roots ∧
      Visit[A,Fin.last A.length] ∈ P.roots := by
  obtain ⟨z, on_sphere⟩ := (NormedSpace.sphere_nonempty (x := (0 : Plane))).mpr zero_le_one
  let u : Metric.closedBall (0 : Plane) 1 :=
    ⟨z, Metric.sphere_subset_closedBall on_sphere⟩
  have norm : ‖(disk (disk.symm u)).val‖ = 1 := by
    rw [disk.apply_symm_apply]
    simpa only [u, dist_zero_right] using (Metric.mem_sphere.mp on_sphere)
  obtain ⟨bank, _⟩ := Set.mem_iUnion.mp
    ((F.bankBoundary_iff_disk_norm_eq_one Set.univ disk (disk.symm u)).mpr norm)
  exact C.exists_contour_starts_ends_root S Q ((C.boundaryEndEquiv Set.univ).symm (bank, false))
    roots

/-- Every positive nonroot defect has its original indexed source event when the
contour starts and ends on the rim. -/
theorem exists_positiveContourSource_of_defect
    (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
    (starts : Visit[Q,0] ∈ P.roots) (ends : Visit[Q,Fin.last Q.length] ∈ P.roots)
    (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)
    (positive : 0 < C.interiorAngularDefect Set.univ vertex) :
    ∃ e : C.PositiveContourSource S Q, C.positiveContourVertex S Q e = vertex := by
  let interval := C.contourParentInterval S Q roots starts vertex nonroot
  let first := finRotate (Q.length + 1) interval.enter
  have at_first : Visit[Q,first] = vertex :=
    C.contourOriginalVertex_after_enter S Q roots starts vertex nonroot
  have early : first.val < Q.length := by
    have diff : first ≠ Fin.last Q.length := fun h => nonroot (at_first ▸ (h.symm ▸ ends))
    have bound := first.isLt
    by_contra! late
    exact diff (Fin.ext (by rw [Fin.val_last]; omega))
  let k : Fin Q.length := ⟨first.val, early⟩
  have at_k : k.castSucc = first := Fin.ext rfl
  have fresh : Visit[Q,first] ∉ (C.contourFrontier S Q first).processed := by
    rw [at_first, C.mem_contourFrontier_processed_iff_enter S Q roots starts vertex nonroot]
    have offset : first.val = interval.enter.val + 1 :=
      C.contourParentInterval_enter_succ_val S Q roots starts vertex nonroot
    exact fun h => (not_lt_of_ge offset.le) h
  have original := (congrArg (C.contourOriginalVertex S Q) at_k).trans at_first
  exact ⟨⟨k, at_k.symm ▸ fresh, original.symm ▸ positive⟩, original⟩

end Unfoldings.TriangleComplex
