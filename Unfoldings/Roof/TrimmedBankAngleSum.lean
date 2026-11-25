module

public import Unfoldings.Roof.TrimmedBankContacts

/-! The original graph-window angle sum is exactly the real saved-bank heading error. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {retain : Set C.Seam} {n : ℕ} (bank : (C.boundarySystem retain).Chain (n + 1))
  (a b : unitInterval)

local notation "P" => K.folding.projectedBoundaryChain bank
local notation "Q" => PolygonalChain.trimEnds (K.folding.projectedBoundaryChain bank) a b
local notation "L" => PolygonalChain.vertex (Q) 0
local notation "R" => PolygonalChain.vertex (Q) (Fin.last (n + 2))
local notation "X" => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0

theorem projectedBank_avoids_faceInteriors (j : Face) :
    Disjoint (interior (K.projectedTriangle j).carrier) (Set.range (P).path) := by
  apply Set.disjoint_left.mpr
  intro z inside hit
  rw [(P).path_range_eq_segments] at hit
  have avoids (i : Fin (n + 2)) :
      Disjoint (interior (K.projectedTriangle j).carrier)
        (segment ℝ ((P).vertex i.castSucc) ((P).vertex i.succ)) := by
    rw [K.projectedBoundaryChain_start_germ bank i, K.projectedBoundaryChain_finish_germ bank i]
    exact K.projectedGerm_segment_disjoint_interior (bank.point i).val j
  rcases hit with first | member
  · exact Set.disjoint_left.mp (avoids 0) inside (first.symm ▸ left_mem_segment ℝ _ _)
  · obtain ⟨i, link⟩ := Set.mem_iUnion.mp member
    exact Set.disjoint_left.mp (avoids i) inside link

open Classical in
set_option maxHeartbeats 1900000 in
/-- With the positive chart orientation, the original upper-side graph
sum is the negative of the actual unreduced intrinsic bank turn error. -/
theorem sum_trimmedGraphWindow_eq_neg_headingError {f : ℝ → ℝ} (hf : Continuous f)
    (progress : ∀ i, 0 < ((P).edge i) 0) (first : a.val < 1) (last : 0 < b.val)
    (trace : graphPoint f '' Set.Icc ((L) 0) ((R) 0) = Set.range (Q).path)
    (in_roof : Set.range (Q).path ⊆ interior K.footprint)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (bank.point i).val))
    (positive : 0 < K.projectedGermOrientation bank.first.val) :
    (∑ w : C.Vertex Set.univ,
      if K.projectedVertex w ∈ graphPoint f '' Set.Ioo ((L) 0) ((R) 0) then
        K.regionalAngleExcess (K.graphWindowFaces f ((L) 0) ((R) 0)) w else 0) =
      -K.projectedMetricHeadingError bank (Fin.last (n + 1)) := by
  let U := K.graphWindowFaces f ((L) 0) ((R) 0)
  let view (i : Fin (n + 1)) := originalBankTurnVertex bank i
  let contact := graphPoint f '' Set.Ioo ((L) 0) ((R) 0)
  have cropped_progress := (P).trimEnds_positive_linear_edges a b first last (X) progress
  have strict := (Q).strictMono_linear_vertices (X) cropped_progress
  have aligned (j : Face) :
      Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc ((L) 0) ((R) 0)) :=
    (K.projectedBank_avoids_faceInteriors bank j).mono_right
      (trace.subset.trans ((P).trimEnds_path_subset a b))
  have names (i : Fin (n + 2)) : (bank.point i).val.1.1 ∈ U ∧
      (C.mateGerm Set.univ (bank.point i).val).1.1 ∉ U := by
    obtain ⟨s, t, ahead, start, finish⟩ := (P).exists_trimmed_link_parameters a b first last i
    have next_edge : (Q).vertex i.castSucc 0 < (Q).vertex i.succ 0 :=
      strict (Fin.castSucc_lt_succ (i := i))
    have in_graph : segment ℝ ((Q).vertex i.castSucc) ((Q).vertex i.succ) ⊆
        graphPoint f '' Set.Icc ((L) 0) ((R) 0) := by
      rw [trace, (Q).path_range_eq_segments]
      exact (Set.subset_iUnion (fun j : Fin (n + 2) =>
        segment ℝ ((Q).vertex j.castSucc) ((Q).vertex j.succ)) i).trans Set.subset_union_right
    simp only [PolygonalChain.point, K.projectedBoundaryChain_start_germ bank i,
      K.projectedBoundaryChain_finish_germ bank i] at start finish
    exact K.graphWindowFaces_on_positive_germ hf aligned (bank.point i).val s t ahead start finish
      next_edge in_graph ((K.projected_boundaryChain_sign bank i).mpr positive) (cut i)
  have at_graph (i : Fin (n + 1)) : K.projectedVertex (view i) ∈ contact :=
    (K.mem_trimmed_bank_graph_iff bank a b progress first last trace (view i)).mpr ⟨i, rfl⟩
  have turn (i : Fin (n + 1)) : K.regionalAngleExcess U (view i) =
      C.totalAngle retain (C.boundaryEndVertex retain (bank.point i.succ)) -
        K.projectedTotalAngle retain (C.boundaryEndVertex retain (bank.point i.succ)) := by
    let p := bank.point i.succ
    let prev := bank.point i.castSucc
    have mate := congrArg (C.boundaryMate retain) (bank.next i)
    change C.boundaryMate retain (C.boundaryMate retain (C.boundaryTurn retain prev)) =
      C.boundaryMate retain p at mate
    rw [C.boundaryMate_involutive] at mate
    have on_bank : K.projectedVertex (view i) ∈ Set.range (Q).path :=
      trace.subset (Set.image_mono Set.Ioo_subset_Icc_self (at_graph i))
    have times : K.projectedVertex (view i) 0 ∈ Set.Ioo ((L) 0) ((R) 0) ∧
        K.projectedVertex (view i) 1 = f (K.projectedVertex (view i) 0) := by
      obtain ⟨t, ht, eq⟩ := at_graph i
      rw [← eq]
      exact ⟨ht, rfl⟩
    apply K.regionalAngleExcess_graphWindow_eq_original_fan hf aligned p (names i.succ).1
      (names i.succ).2 _ _ (view i) rfl (in_roof on_bank) times.1 times.2
    · rw [← mate, C.boundaryTurn_face]
      exact (names i.castSucc).1
    · rw [← mate, C.mateGerm_boundaryTurn_face _ (cut i.castSucc)]
      exact (names i.castSucc).2
  have injective : Function.Injective view := by
    intro i j same
    have pi := K.projected_originalBankTurnVertex_eq_trim bank a b i
    have pj := K.projected_originalBankTurnVertex_eq_trim bank a b j
    have coords := congrArg (fun p : Plane => p 0)
      (pi.symm.trans ((congrArg K.projectedVertex same).trans pj))
    have indices := congrArg Fin.val (strict.injective coords)
    apply Fin.ext
    change i.val + 1 = j.val + 1 at indices
    omega
  have indexed : (Finset.univ.filter (fun w : C.Vertex Set.univ => K.projectedVertex w ∈ contact)) =
      Finset.univ.image view := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact (K.mem_trimmed_bank_graph_iff bank a b progress first last trace w).trans
      ⟨fun ⟨i, eq⟩ => ⟨i, eq.symm⟩, fun ⟨i, eq⟩ => ⟨i, eq.symm⟩⟩
  have named :
      (∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ contact then K.regionalAngleExcess U w else 0) =
        ∑ i, K.regionalAngleExcess U (view i) := by
    rw [← Finset.sum_filter, indexed, Finset.sum_image injective.injOn]
  change (∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ contact then
    K.regionalAngleExcess U w else 0) = _
  rw [named]
  simp_rw [turn]
  rw [projectedMetricHeadingError, K.projectedMetricHeading_eq, TriangleComplex.boundaryChainRollHeading]
  have full (g : Fin (n + 1) → ℝ) : Fin.partialSum g (Fin.last (n + 1)) = ∑ i, g i := by
    rw [Fin.partialSum, List.sum_take_ofFn, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    exact ite_eq_left i.isLt
  rw [full, full, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Unfoldings.ConvexRoof
