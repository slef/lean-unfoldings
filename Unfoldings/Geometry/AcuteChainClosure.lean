module

public import Unfoldings.Geometry.TwoLinkChainClosure
public import Unfoldings.Geometry.PolygonalVertexRays
public import Mathlib.Tactic.FinCases

/-! A strict choice of the apex preserves both closing contacts of an acute chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane n) (c : Plane)

local notation "a" => P.vertex 0
local notation "b" => P.vertex (Fin.last n)

/-- Closing links in terminal, then initial, order. -/
def twoClosingLinks : Fin 2 → Plane × Plane := ![(b, c), (c, a)]

open Classical in
/-- The three corners of the closure, with any coincidences counted once. -/
def twoClosingCorners : Finset Plane := {a, b, c}

/-- Join the chain's endpoints to one apex. -/
def twoLinkClosure : Set Plane := Set.range P.path ∪ (segment ℝ b c ∪ segment ℝ c a)

variable (h k : Plane →L[ℝ] ℝ)
  (first : ∀ i, 0 < h (P.edge i)) (last : ∀ i, 0 < k (P.edge i))

include first in
theorem strictMono_linear_vertices : StrictMono (h ∘ P.vertex) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact sub_pos.mp ((map_sub h _ _).symm ▸ first i)

include first in
theorem vertex_not_mem_openSegment_of_linear_progress (j : Fin (n + 1)) (i : Fin n) :
    P.vertex j ∉ openSegment ℝ (P.vertex i.castSucc) (P.vertex i.succ) := by
  rintro member
  have interior_value : h (P.vertex j) ∈ openSegment ℝ
      (h (P.vertex i.castSucc)) (h (P.vertex i.succ)) := by
    change h.toLinearMap.toAffineMap (P.vertex j) ∈ openSegment ℝ
      (h.toLinearMap.toAffineMap (P.vertex i.castSucc)) (h.toLinearMap.toAffineMap (P.vertex i.succ))
    rw [← image_openSegment ℝ h.toLinearMap.toAffineMap]
    exact Set.mem_image_of_mem h member
  have strict := P.strictMono_linear_vertices h first
  have increasing : h (P.vertex i.castSucc) < h (P.vertex i.succ) :=
    strict (Fin.castSucc_lt_succ (i := i))
  rw [openSegment_eq_Ioo increasing] at interior_value
  have after := strict.lt_iff_lt.mp interior_value.1
  have before := strict.lt_iff_lt.mp interior_value.2
  change i.val < j.val at after
  change j.val < i.val + 1 at before
  omega

variable (initial : h c ≤ h (P.vertex 0)) (terminal : k (P.vertex (Fin.last n)) ≤ k c)

include first last initial terminal in
theorem twoClosingLinks_inter_subset (nonempty : 0 < n) :
    segment ℝ b c ∩ segment ℝ c a ⊆ {c} := by
  intro z member
  obtain ⟨t, ht, to_b⟩ := (segment_eq_image_lineMap ℝ c b).subset
    ((segment_symm ℝ b c) ▸ member.1)
  obtain ⟨s, hs, to_a⟩ := (segment_eq_image_lineMap ℝ c a).subset member.2
  have compare (L : Plane →L[ℝ] ℝ) : t * (L b - L c) = s * (L a - L c) := by
    have eq := congrArg L (to_b.trans to_a.symm)
    change L.toLinearMap.toAffineMap (AffineMap.lineMap c b t) =
      L.toLinearMap.toAffineMap (AffineMap.lineMap c a s) at eq
    rw [L.toLinearMap.toAffineMap.apply_lineMap, L.toLinearMap.toAffineMap.apply_lineMap] at eq
    change AffineMap.lineMap (L c) (L b) t = AffineMap.lineMap (L c) (L a) s at eq
    simp only [AffineMap.lineMap_apply_ring'] at eq
    linarith only [eq]
  have ends : (0 : Fin (n + 1)) < Fin.last n := by
    exact nonempty
  have h_lt := P.strictMono_linear_vertices h first ends
  have k_lt := P.strictMono_linear_vertices k last ends
  change h a < h b at h_lt
  change k a < k b at k_lt
  have h_eq := compare h
  have k_eq := compare k
  by_cases zero : t = 0
  · simpa only [Set.mem_singleton_iff, zero, AffineMap.lineMap_apply_zero] using to_b.symm
  · have t_pos := lt_of_le_of_ne ht.1 (Ne.symm zero)
    have diff : 0 < t * (h b - h a) := mul_pos t_pos (sub_pos.mpr h_lt)
    have larger : t < s := by
      by_contra! rev
      have := mul_le_mul_of_nonneg_right rev (sub_nonneg.mpr initial)
      nlinarith only [h_eq, diff, this]
    have s_pos := t_pos.trans larger
    have diff' : 0 < s * (k b - k a) := mul_pos s_pos (sub_pos.mpr k_lt)
    have bound := mul_le_mul_of_nonneg_right larger.le (sub_nonneg.mpr terminal)
    exfalso
    nlinarith only [k_eq, diff', bound]

include first last initial terminal in
theorem twoLinkClosure_contacts (nonempty : 0 < n) :
    Set.range P.path ∩ (segment ℝ b c ∪ segment ℝ c a) ⊆ {a, b} := by
  rintro z ⟨trace, on_final | on_initial⟩
  · have linear : k z ∈ segment ℝ (k b) (k c) := by
      change k.toLinearMap.toAffineMap z ∈ segment ℝ
        (k.toLinearMap.toAffineMap b) (k.toLinearMap.toAffineMap c)
      rw [← image_segment ℝ k.toLinearMap.toAffineMap]
      exact Set.mem_image_of_mem k on_final
    rw [segment_eq_Icc terminal] at linear
    have equal := le_antisymm (P.path_linear_bounds k (fun i => (last i).le) trace).2 linear.1
    have last_point : z = b := P.path_linear_injOn k (fun i => (last i).le)
      (fun i zero => ((last i).ne' zero).elim) nonempty trace ⟨1, P.path.target⟩ equal
    exact Or.inr last_point
  · have linear : h z ∈ segment ℝ (h c) (h a) := by
      change h.toLinearMap.toAffineMap z ∈ segment ℝ
        (h.toLinearMap.toAffineMap c) (h.toLinearMap.toAffineMap a)
      rw [← image_segment ℝ h.toLinearMap.toAffineMap]
      exact Set.mem_image_of_mem h on_initial
    rw [segment_eq_Icc initial] at linear
    have equal := le_antisymm linear.2 (P.path_linear_bounds h (fun i => (first i).le) trace).1
    have first_point : z = a := P.path_linear_injOn h (fun i => (first i).le)
      (fun i zero => ((first i).ne' zero).elim) nonempty trace ⟨0, P.path.source⟩ equal
    exact Or.inl first_point

include first last initial terminal in
/-- The apex can move into an open quadrant, so generic connectors can be chosen. -/
theorem isJordanCurve_twoLinkClosure (nonempty : 0 < n) :
    Schoenflies.IsJordanCurve (P.twoLinkClosure c) := by
  have ends : (0 : Fin (n + 1)) < Fin.last n := nonempty
  have h_lt := P.strictMono_linear_vertices h first ends
  have k_lt := P.strictMono_linear_vertices k last ends
  change h a < h b at h_lt
  change k a < k b at k_lt
  have first_ne : c ≠ a := fun same => k_lt.not_ge (same ▸ terminal)
  have last_ne : b ≠ c := fun same => h_lt.not_ge (same.symm ▸ initial)
  have closing := (Schoenflies.isArcBetween_segment last_ne).concatenate
    (Schoenflies.isArcBetween_segment first_ne) (fun z hz hw =>
      P.twoClosingLinks_inter_subset c h k first last initial terminal nonempty ⟨hz, hw⟩)
  exact Schoenflies.IsJordanCurve.of_two_arcs (P.isArcBetween_of_linear_progress h nonempty first)
    closing (fun z bank links =>
      P.twoLinkClosure_contacts c h k first last initial terminal nonempty ⟨bank, links⟩)

end Unfoldings.PolygonalChain
