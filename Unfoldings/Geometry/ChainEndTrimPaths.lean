module

public import Unfoldings.Geometry.ChainEndTrimming
public import Unfoldings.Geometry.RadialGraphArc

/-! Endpoint trimming preserves the actual path carrier order and radial progress. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

/-- The corresponding original parameter on the same edge after trimming. -/
def trimEndsParameter (a b : unitInterval) (i : Fin (n + 2)) (t : unitInterval) : unitInterval :=
  if i.val = 0 then
    ⟨(a : ℝ) + (1 - (a : ℝ)) * (t : ℝ),
      add_nonneg a.property.1 (mul_nonneg (sub_nonneg.mpr a.property.2) t.property.1), by
        have bound := mul_le_mul_of_nonneg_left t.property.2 (sub_nonneg.mpr a.property.2)
        nlinarith⟩
  else if i.val = n + 1 then
    ⟨(b : ℝ) * (t : ℝ), mul_nonneg b.property.1 t.property.1,
      (mul_le_mul_of_nonneg_left t.property.2 b.property.1).trans (by simpa using b.property.2)⟩
  else t

theorem monotone_trimEndsParameter (a b : unitInterval) (i : Fin (n + 2)) :
    Monotone (trimEndsParameter a b i) := by
  intro t s ordered
  unfold trimEndsParameter
  split_ifs
  · exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left ordered (sub_nonneg.mpr a.property.2))
  · exact mul_le_mul_of_nonneg_left ordered b.property.1
  · exact ordered

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : PolygonalChain E (n + 2))

/-- Every trimmed link is an increasing affine subparametrization of the same original link. -/
theorem trimEnds_point (a b : unitInterval) (i : Fin (n + 2)) (t : unitInterval) :
    (P.trimEnds a b).point i t = P.point i (trimEndsParameter a b i t) := by
  by_cases first : i.val = 0
  · have same : i = 0 := Fin.ext first
    subst i
    rw [point, Fin.castSucc_zero, P.trimEnds_start,
      P.trimEnds_vertex_internal a b _ (by simp) (by simp)]
    simp only [trimEndsParameter, Fin.val_zero, ite_true, point, AffineMap.lineMap_apply_module']
    module
  · by_cases last : i.val = n + 1
    · have same : i = Fin.last (n + 1) := Fin.ext last
      subst i
      rw [point, Fin.succ_last, P.trimEnds_last,
        P.trimEnds_vertex_internal a b _ (by simp) (by simp)]
      simp only [trimEndsParameter, Fin.val_last, ite_eq_right (by omega : ¬ n + 1 = 0),
        ite_true, point, AffineMap.lineMap_apply_module']
      module
    · rw [point, P.trimEnds_vertex_internal a b i.castSucc
        (by change 0 < i.val; omega) (by change i.val < n + 2; omega),
        P.trimEnds_vertex_internal a b i.succ
          (by change 0 < i.val + 1; omega) (by change i.val + 1 < n + 2; omega)]
      simp only [trimEndsParameter, ite_eq_right first, ite_eq_right last]
      rfl

/-- Trimming adds no carrier points and keeps every intermediate original corner. -/
theorem trimEnds_path_subset (a b : unitInterval) :
    Set.range (P.trimEnds a b).path ⊆ Set.range P.path := by
  intro z member
  rw [(P.trimEnds a b).path_range] at member
  rcases member with initial | member
  · rw [Set.mem_singleton_iff.mp initial, P.trimEnds_start]
    exact P.point_mem_path_range 0 a
  · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp member
    rw [P.trimEnds_point]
    exact P.point_mem_path_range _ _

/-- Every whole-edge radial test survives both exact endpoint subparametrizations. -/
theorem trimEnds_radialFrom (a b : unitInterval) {source : E} (radial : P.RadialFrom source 0) :
    (P.trimEnds a b).RadialFrom source 0 := by
  intro i _ t s ordered
  change dist source ((P.trimEnds a b).point i t) ≤ dist source ((P.trimEnds a b).point i s)
  rw [P.trimEnds_point, P.trimEnds_point]
  exact radial i (Nat.zero_le _) (monotone_trimEndsParameter a b i ordered)

/-- A nonzero final link and a positive final fraction retain strict endpoint radial progress. -/
theorem trimEnds_radius_progress (a b : unitInterval) {source : E}
    (radial : P.RadialFrom source 0) (last_nonzero : P.edge (Fin.last (n + 1)) ≠ 0)
    (positive : 0 < (b : ℝ)) :
    dist source ((P.trimEnds a b).vertex 0) <
      dist source ((P.trimEnds a b).vertex (Fin.last (n + 2))) := by
  rw [P.trimEnds_start, P.trimEnds_last]
  have before := radial.dist_point_le P 0 (Fin.last (n + 1)) a 0 (Nat.zero_le _) (Or.inl (by
    change (0 : ℕ) < n + 1
    omega))
  have outward := (monotone_dist_lineMap_iff _ _ _).mp (radial (Fin.last (n + 1)) (Nat.zero_le _))
  have different : P.vertex (Fin.last (n + 1)).castSucc ≠
      P.vertex (Fin.last (n + 1)).succ := by
    intro same
    apply last_nonzero
    simp only [edge, same, sub_self]
  have strict := dist_lineMap_lt_of_inner_nonneg source _ _ outward different
    (show (0 : ℝ) ≤ 0 from le_rfl) positive
  exact before.trans_lt strict

end Unfoldings.PolygonalChain
