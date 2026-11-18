module

public import Unfoldings.Geometry.BankGapModel
public import Unfoldings.Geometry.PolygonalRayOpening

/-! Actual closed-edge and whole-tail bank marks have exact intrinsic speeds. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.BankGapModel

variable {n : ℕ} {first second : PolygonalRay ℂ n} (M : BankGapModel first second)

/-- Retain a literal closed-edge point on either constructed gap bank. -/
def edgePoint (side : Bool) (i : Fin n) (t : unitInterval) : PolygonalPoint M.region :=
  M.bankPoint side ⟨(M.bank side).chain.point i t, Or.inl (by
    rw [(M.bank side).chain.path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, t, rfl⟩))⟩

/-- Retain every original infinite-tail parameter, including its true initial point. -/
def tailPoint (side : Bool) (t : ℝ≥0) : PolygonalPoint M.region :=
  M.bankPoint side ⟨(M.bank side).tail t, (M.bank side).tail_mem t⟩

@[simp] theorem edgePoint_val (side : Bool) (i : Fin n) (t : unitInterval) :
    (M.edgePoint side i t).val = (M.bank side).chain.point i t := rfl

@[simp] theorem tailPoint_val (side : Bool) (t : ℝ≥0) :
    (M.tailPoint side t).val = (M.bank side).tail t := rfl

/-- Every point of the same original edge segment stays on the actual gap boundary. -/
theorem edge_segment_subset (side : Bool) (i : Fin n) (s t : unitInterval) :
    segment ℝ (M.edgePoint side i s).val (M.edgePoint side i t).val ⊆ M.region := by
  have range_eq : Set.range ((M.bank side).chain.point i) =
      segment ℝ ((M.bank side).chain.vertex i.castSucc)
        ((M.bank side).chain.vertex i.succ) := Path.range_segment _ _
  have inside (u : unitInterval) : (M.bank side).chain.point i u ∈
      segment ℝ ((M.bank side).chain.vertex i.castSucc)
        ((M.bank side).chain.vertex i.succ) := range_eq ▸ Set.mem_range_self u
  intro z member
  have in_edge := (convex_segment _ _).segment_subset (inside s) (inside t) member
  obtain ⟨u, rfl⟩ := range_eq.symm ▸ in_edge
  exact (M.edgePoint side i u).property

/-- Intrinsic distances on each entire gap edge equal their actual Euclidean distances. -/
theorem edist_edgePoint (side : Bool) (i : Fin n) (s t : unitInterval) :
    edist (M.edgePoint side i s) (M.edgePoint side i t) =
      (‖(M.bank side).chain.edge i‖₊ : ℝ≥0∞) * edist s t := by
  rw [PolygonalPoint.edist_eq_of_segment (M.edge_segment_subset side i s t)]
  simp only [edgePoint_val, PolygonalChain.point, AffineMap.lineMap_apply_module']
  rw [edist_dist, edist_dist, dist_eq_norm, add_sub_add_right_eq_sub, ← sub_smul,
    norm_smul, Real.norm_eq_abs]
  change ENNReal.ofReal (|s.val - t.val| * ‖(M.bank side).chain.edge i‖) = _
  rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ofReal_norm, enorm_eq_nnnorm]
  rfl

/-- The entire actual tail is a convex subset of the gap boundary. -/
theorem convex_range_tail (side : Bool) : Convex ℝ (Set.range (M.bank side).tail) := by
  rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩ a b ha hb sum
  refine ⟨⟨a * s.val + b * t.val,
    add_nonneg (mul_nonneg ha s.property) (mul_nonneg hb t.property)⟩, ?_⟩
  have affine (p d : ℂ) (s t a b : ℝ) (sum : a + b = 1) :
      p + (a * s + b * t) • d = a • (p + s • d) + b • (p + t • d) := by
    calc
      _ = (a + b) • p + (a * s + b * t) • d := by rw [sum, one_smul]
      _ = _ := by module
  exact affine _ _ _ _ _ _ sum

/-- Intrinsic distances on the whole tail have their original constant speed. -/
theorem edist_tailPoint (side : Bool) (s t : ℝ≥0) :
    edist (M.tailPoint side s) (M.tailPoint side t) =
      (‖(M.bank side).direction‖₊ : ℝ≥0∞) * edist s t := by
  have inside : segment ℝ (M.tailPoint side s).val (M.tailPoint side t).val ⊆ M.region := by
    intro z member
    obtain ⟨u, rfl⟩ := (M.convex_range_tail side).segment_subset
      (Set.mem_range_self s) (Set.mem_range_self t) member
    exact (M.tailPoint side u).property
  rw [PolygonalPoint.edist_eq_of_segment inside]
  simp only [tailPoint_val, PolygonalRay.tail]
  rw [edist_dist, edist_dist, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul,
    norm_smul, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
    ofReal_norm, enorm_eq_nnnorm]
  rfl

variable {R : PolygonalRay ℂ n} {events : List (PolygonalChain.Opening n)}
  (N : BankGapModel R (R.openings events))

/-- Every opening preserves both marked sides' intrinsic closed-edge distances exactly. -/
theorem edist_edgePoint_sides (i : Fin n) (s t : unitInterval) :
    edist (N.edgePoint false i s) (N.edgePoint false i t) =
      edist (N.edgePoint true i s) (N.edgePoint true i t) := by
  rw [N.edist_edgePoint, N.edist_edgePoint]
  have length : ‖(R.openings events).chain.edge i‖ = ‖R.chain.edge i‖ := by
    rw [R.openings_chain, R.chain.openings_edge, norm_mul, norm_polarRay, one_mul]
  change (‖R.chain.edge i‖₊ : ℝ≥0∞) * edist s t =
    (‖(R.openings events).chain.edge i‖₊ : ℝ≥0∞) * edist s t
  rw [show ‖(R.openings events).chain.edge i‖₊ = ‖R.chain.edge i‖₊ from Subtype.ext length]

/-- The infinite banks retain the same speed after every finite sequence of openings. -/
theorem edist_tailPoint_sides (s t : ℝ≥0) :
    edist (N.tailPoint false s) (N.tailPoint false t) =
      edist (N.tailPoint true s) (N.tailPoint true t) := by
  rw [N.edist_tailPoint, N.edist_tailPoint]
  have speed : ‖(R.openings events).direction‖ = ‖R.direction‖ := by
    rw [R.openings_direction, norm_mul, norm_polarRay, one_mul]
  change (‖R.direction‖₊ : ℝ≥0∞) * edist s t =
    (‖(R.openings events).direction‖₊ : ℝ≥0∞) * edist s t
  rw [show ‖(R.openings events).direction‖₊ = ‖R.direction‖₊ from Subtype.ext speed]

end Unfoldings.BankGapModel
