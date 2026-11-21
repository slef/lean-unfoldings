module

public import Unfoldings.Roof.CompatibleCutPieces
public import Unfoldings.Roof.CompatiblePotentialPaths
public import Unfoldings.Geometry.RadialNormProgress

/-! A genuine routed link has a fixed directed carrier, including terminal rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompatiblePotentialRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {U : Set Face} {G : SlopeEnvelope} {boundary : (frontier G.slopes).Nonempty}
  {a β : ℝ} (R : K.CompatiblePotentialRouting U G boundary a β)

open Classical in
/-- Every original vertex starts one piece, a finite parent edge or a terminal ray. -/
def cutPieceDirection (v : C.Vertex Set.univ) : Plane :=
  if root : v ∈ R.parents.roots then
    R.exterior.direction (R.exterior.slope (R.terminalIndex ⟨v, root⟩))
  else R.parentDirection v

theorem cutPieceDirection_nonroot {v : C.Vertex Set.univ} (nonroot : v ∉ R.parents.roots) :
    R.cutPieceDirection v = R.parentDirection v := by
  rw [cutPieceDirection, dite_eq_right nonroot]

theorem cutPieceDirection_terminal (v : {v // v ∈ R.parents.roots}) :
    R.cutPieceDirection v.val = R.exterior.direction (R.exterior.slope (R.terminalIndex v)) := by
  rw [cutPieceDirection, dite_eq_left v.property]

def cutPiecePoint (v : C.Vertex Set.univ) (t : ℝ) : Plane :=
  K.projectedVertex v + t • R.cutPieceDirection v

theorem cutPiecePoint_nonroot_add {v : C.Vertex Set.univ}
    (nonroot : v ∉ R.parents.roots) (t : ℝ) :
    R.cutPiecePoint v t = K.projectedVertex v + t • R.parentDirection v := by
  rw [cutPiecePoint, R.cutPieceDirection_nonroot nonroot]

theorem cutPiecePoint_zero (v : C.Vertex Set.univ) :
    R.cutPiecePoint v 0 = K.projectedVertex v := by simp [cutPiecePoint]

theorem cutPiecePoint_nonroot {v : C.Vertex Set.univ} (nonroot : v ∉ R.parents.roots) (t : ℝ) :
    R.cutPiecePoint v t = AffineMap.lineMap (K.projectedVertex v)
      (K.projectedVertex (R.parents.parent v)) t := by
  rw [cutPiecePoint, cutPieceDirection, dite_eq_right nonroot, AffineMap.lineMap_apply_module', add_comm]
  rfl

theorem cutPiecePoint_terminal (v : {v // v ∈ R.parents.roots}) (t : ℝ) :
    R.cutPiecePoint v.val t = R.exterior.ray (R.terminalIndex v) t := by
  rw [cutPiecePoint, cutPieceDirection, dite_eq_left v.property]
  simp only [SlopeEnvelope.ExteriorPlan.ray, R.exterior_points, terminalIndex]

theorem cutPieceDirection_ne_zero (v : C.Vertex Set.univ) : R.cutPieceDirection v ≠ 0 := by
  unfold cutPieceDirection
  split_ifs with root
  · exact norm_ne_zero_iff.mp (by rw [R.exterior.unit]; norm_num)
  · intro zero
    have eq := K.projectedVertex_injective (sub_eq_zero.mp zero)
    have strict := R.parents.ascending v root
    rw [eq] at strict
    exact lt_irrefl _ strict

theorem cutPiecePoint_injective (v : C.Vertex Set.univ) :
    Function.Injective (R.cutPiecePoint v) := by
  intro s t same
  have equal : s • R.cutPieceDirection v = t • R.cutPieceDirection v := add_left_cancel same
  exact smul_left_injective ℝ (R.cutPieceDirection_ne_zero v) equal

/-- An oriented nonzero link, with its carrier and both actual parameters. -/
structure DirectedCutStep (x y : Plane) where
  vertex : C.Vertex Set.univ
  first : ℝ
  last : ℝ
  first_nonneg : 0 ≤ first
  ordered : first < last
  finite : vertex ∉ R.parents.roots → last ≤ 1
  first_eq : x = R.cutPiecePoint vertex first
  last_eq : y = R.cutPiecePoint vertex last

/-- A genuine routed link selects a directed piece. -/
theorem nonempty_directedCutStep_of_follows {x y : Plane} (step : R.FollowsStep x y)
    (genuine : x ≠ y) : Nonempty (R.DirectedCutStep x y) := by
  rcases step with ⟨v, s, t, hs, order, ht, hx, hy⟩ | ⟨v, s, t, hs, order, hx, hy⟩
  · have px : x = R.cutPiecePoint v.val s := by
      rw [hx, cutPiecePoint, cutPieceDirection, dite_eq_right v.property]
    have py : y = R.cutPiecePoint v.val t := by
      rw [hy, cutPiecePoint, cutPieceDirection, dite_eq_right v.property]
    exact ⟨⟨v.val, s, t, hs, order.lt_of_ne (fun same =>
      genuine (px.trans (same ▸ py.symm))), fun _ => ht, px, py⟩⟩
  · rw [← R.cutPiecePoint_terminal] at hx hy
    exact ⟨⟨v.val, s, t, hs, order.lt_of_ne (fun same =>
      genuine (hx.trans (same ▸ hy.symm))), fun not_root => (not_root v.property).elim, hx, hy⟩⟩

theorem cutPiecePoint_terminal_mem_openPiece (v : {v // v ∈ R.parents.roots})
    {t : ℝ} (positive : 0 < t) : R.cutPiecePoint v.val t ∈ R.openPiece v.val := by
  rw [R.cutPiecePoint_terminal v]
  let r := R.terminalIndex v
  have terminal : r ∈ R.exterior.terminal := v.property.2
  rw [show v.val = r.val from rfl, R.openPiece_root r, R.exterior.terminal_openPiece_eq terminal]
  exact ⟨t, positive, rfl⟩

theorem cutPiecePoint_finite_mem_openPiece {v : C.Vertex Set.univ} (nonroot : v ∉ R.parents.roots)
    {t : ℝ} (positive : 0 < t) (before : t < 1) : R.cutPiecePoint v t ∈ R.openPiece v := by
  rw [R.cutPiecePoint_nonroot nonroot]
  apply R.parent_segment_subset_openPiece nonroot
  rw [openSegment_eq_image_lineMap]
  exact ⟨t, ⟨positive, before⟩, rfl⟩

namespace DirectedCutStep

variable {R} {x y : Plane} (S : R.DirectedCutStep x y)

theorem first_mem_openPiece (positive : 0 < S.first) : x ∈ R.openPiece S.vertex := by
  apply Eq.mpr (congrArg (fun p => p ∈ R.openPiece S.vertex) S.first_eq)
  by_cases root : S.vertex ∈ R.parents.roots
  · exact R.cutPiecePoint_terminal_mem_openPiece ⟨S.vertex, root⟩ positive
  · exact R.cutPiecePoint_finite_mem_openPiece root positive
      (S.ordered.trans_le (S.finite root))

theorem last_mem_openPiece_or_vertex :
    y ∈ R.openPiece S.vertex ∨ ∃ w, y = K.projectedVertex w := by
  apply Eq.mpr (congrArg (fun p => p ∈ R.openPiece S.vertex ∨ ∃ w, p = K.projectedVertex w)
    S.last_eq)
  have positive := S.first_nonneg.trans_lt S.ordered
  by_cases root : S.vertex ∈ R.parents.roots
  · exact Or.inl (R.cutPiecePoint_terminal_mem_openPiece ⟨S.vertex, root⟩ positive)
  · rcases (S.finite root).lt_or_eq with before | finish
    · exact Or.inl (R.cutPiecePoint_finite_mem_openPiece root positive before)
    · exact Or.inr ⟨R.parents.parent S.vertex, by
        rw [finish, R.cutPiecePoint_nonroot root, AffineMap.lineMap_apply_one]⟩

/-- Scale the full carrier direction to the exact next physical edge. -/
theorem radial_margin_of_carrier {q : Plane} {γ : ℝ}
    (margin : γ * (‖x - q‖ * ‖R.cutPieceDirection S.vertex‖) ≤
      inner ℝ (x - q) (R.cutPieceDirection S.vertex)) :
    γ * (‖x - q‖ * ‖y - x‖) ≤ inner ℝ (x - q) (y - x) := by
  have edge : y - x = (S.last - S.first) • R.cutPieceDirection S.vertex := by
    refine (congrArg₂ (· - ·) S.last_eq S.first_eq).trans ?_
    simp only [cutPiecePoint]
    module
  have positive : 0 < S.last - S.first := sub_pos.mpr S.ordered
  rw [edge, norm_smul, Real.norm_eq_abs, abs_of_pos positive, real_inner_smul_right]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left margin positive.le

/-- An earlier point of the same piece is already exactly radial. -/
theorem radial_margin_of_same_piece {q : Plane} {γ t : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (earlier : t ≤ S.first) (at_q : q = R.cutPiecePoint S.vertex t) :
    γ * (‖x - q‖ * ‖y - x‖) ≤ inner ℝ (x - q) (y - x) := by
  apply S.radial_margin_of_carrier
  have displacement : x - q = (S.first - t) • R.cutPieceDirection S.vertex := by
    refine (congrArg₂ (· - ·) S.first_eq at_q).trans ?_
    simp only [cutPiecePoint]
    module
  have margin : γ * (‖(0 : Plane)‖ * ‖R.cutPieceDirection S.vertex‖) ≤
      inner ℝ 0 (R.cutPieceDirection S.vertex) := by simp
  have h := inner_radial_margin_add_smul 0 (R.cutPieceDirection S.vertex)
    nonnegative small (sub_nonneg.mpr earlier) margin
  simpa only [displacement, zero_add] using h

end DirectedCutStep
end Unfoldings.ConvexRoof.CompatiblePotentialRouting
