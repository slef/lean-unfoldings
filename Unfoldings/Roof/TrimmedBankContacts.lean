module

public import Unfoldings.Roof.TrimmedBankGraph

/-! Between the two trims, the only original graph vertices are the saved bank's actual turns. -/

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

/-- The physical vertex underlying the saved fan at a turn of the bank. -/
def originalBankTurnVertex (i : Fin (n + 1)) : C.Vertex Set.univ :=
  C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain (bank.point i.succ))

theorem projected_originalBankTurnVertex (i : Fin (n + 1)) :
    K.projectedVertex (originalBankTurnVertex bank i) = (P).vertex i.succ.castSucc := by
  rw [K.folding.projectedBoundaryChain_vertex_castSucc, K.folding.boundaryPosition_raw]
  rfl

/-- Trimming preserves the exact physical positions of all original bank turns. -/
theorem projected_originalBankTurnVertex_eq_trim (i : Fin (n + 1)) :
    K.projectedVertex (originalBankTurnVertex bank i) = (Q).vertex i.succ.castSucc := by
  rw [K.projected_originalBankTurnVertex, (P).trimEnds_vertex_internal a b _]
  · change 0 < i.val + 1
    omega
  · change i.val + 1 < n + 2
    omega

set_option maxHeartbeats 1800000 in
/-- No original corner in the open graph window is lost or duplicated by
trimming, and no open interior of an original link can add a corner. -/
theorem mem_trimmed_bank_graph_iff {f : ℝ → ℝ}
    (progress : ∀ i, 0 < ((P).edge i) 0) (first : a.val < 1) (last : 0 < b.val)
    (trace : graphPoint f '' Set.Icc ((L) 0) ((R) 0) = Set.range (Q).path)
    (w : C.Vertex Set.univ) :
    K.projectedVertex w ∈ graphPoint f '' Set.Ioo ((L) 0) ((R) 0) ↔
      ∃ i : Fin (n + 1), w = originalBankTurnVertex bank i := by
  have cropped_progress := (P).trimEnds_positive_linear_edges a b first last (X) progress
  have strict := (Q).strictMono_linear_vertices (X) cropped_progress
  have subset := (P).trimEnds_path_subset a b
  have first_bound := ((P).path_linear_bounds (X) (fun i => (progress i).le)
    (subset ((Q).vertex_mem_path_range 0))).1
  have last_bound := ((P).path_linear_bounds (X) (fun i => (progress i).le)
    (subset ((Q).vertex_mem_path_range (Fin.last (n + 2))))).2
  constructor
  · intro member
    have time : K.projectedVertex w 0 ∈ Set.Ioo ((L) 0) ((R) 0) := by
      obtain ⟨t, ht, equal⟩ := member
      rw [← equal]
      exact ht
    have all := subset (trace.subset (Set.image_mono Set.Ioo_subset_Icc_self member))
    have left : K.projectedVertex w ≠ (P).vertex 0 := fun equal =>
      (first_bound.trans_lt time.1).ne (congrArg (fun p : Plane => p 0) equal).symm
    have right : K.projectedVertex w ≠ (P).vertex (Fin.last (n + 2)) := fun equal =>
      (time.2.trans_le last_bound).ne (congrArg (fun p : Plane => p 0) equal)
    have vertex : ∃ j, K.projectedVertex w = (P).vertex j := by
      rw [(P).path_range_eq_segments] at all
      rcases all with start | other
      · exact (left start).elim
      obtain ⟨i, segment⟩ := Set.mem_iUnion.mp other
      by_cases at_start : K.projectedVertex w = (P).vertex i.castSucc
      · exact ⟨i.castSucc, at_start⟩
      by_cases at_end : K.projectedVertex w = (P).vertex i.succ
      · exact ⟨i.succ, at_end⟩
      have open_link := mem_openSegment_of_ne_left_right (Ne.symm at_start) (Ne.symm at_end) segment
      rw [K.projectedBoundaryChain_start_germ bank i, K.projectedBoundaryChain_finish_germ bank i] at open_link
      exact (K.projectedVertex_not_mem_openGermSegment (bank.point i).val w open_link).elim
    obtain ⟨j, position⟩ := vertex
    have not_first : j.val ≠ 0 := fun eq => left (position.trans (congrArg (P).vertex (Fin.ext eq)))
    have not_last : j.val ≠ n + 2 := fun eq => right (position.trans (congrArg (P).vertex (Fin.ext eq)))
    let i : Fin (n + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have index : i.succ.castSucc = j := by
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    refine ⟨i, K.projectedVertex_injective ?_⟩
    rw [K.projected_originalBankTurnVertex, index]
    exact position
  · rintro ⟨i, rfl⟩
    rw [K.projected_originalBankTurnVertex_eq_trim bank a b i]
    have lower : (0 : Fin (n + 3)) < i.succ.castSucc := by change 0 < i.val + 1; omega
    have upper : i.succ.castSucc < Fin.last (n + 2) := by change i.val + 1 < n + 2; omega
    have window : (Q).vertex i.succ.castSucc 0 ∈ Set.Ioo ((L) 0) ((R) 0) :=
      ⟨strict lower, strict upper⟩
    obtain ⟨s, _, equal⟩ := trace.symm.subset ((Q).vertex_mem_path_range i.succ.castSucc)
    refine ⟨s, ?_, equal⟩
    have index : s = (Q).vertex i.succ.castSucc 0 := congrArg (fun p : Plane => p 0) equal
    rwa [index]

end Unfoldings.ConvexRoof
