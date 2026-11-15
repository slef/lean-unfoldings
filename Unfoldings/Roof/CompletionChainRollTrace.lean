module

public import Unfoldings.Roof.CompletionChainRollPositions
public import Unfoldings.Geometry.FiniteInterpolation

/-! Ordered pointwise refinement of whole intrinsic rolls, with exact path images. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainRollTraceIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- The normalized actual intrinsic arclength of every fine vertex in an original bank. -/
def blockParameter (i : Fin (n + 1)) (k : Fin ((R.block i).length + 2)) : unitInterval :=
  ⟨Fin.partialSum (R.blockLengths i) k / C.boundaryBankLength (coarse.point i), by
    have bounds := PolygonalChain.partialSum_bounds (R.blockLengths i)
      (fun k => (E.originalComplex.boundaryBankLength_pos _).le) k
    have total : (∑ k, R.blockLengths i k) = C.boundaryBankLength (coarse.point i) :=
      R.block_sum_lengths i
    exact ⟨div_nonneg bounds.1 (C.boundaryBankLength_pos _).le,
      (div_le_one (C.boundaryBankLength_pos _)).mpr (total ▸ bounds.2)⟩⟩

open Classical in
@[simp] theorem blockParameter_zero (i : Fin (n + 1)) : R.blockParameter i 0 = 0 := by
  apply Subtype.ext
  simp only [blockParameter, Fin.partialSum_zero, zero_div, Set.Icc.coe_zero]

open Classical in
@[simp] theorem blockParameter_last (i : Fin (n + 1)) :
    R.blockParameter i (Fin.last ((R.block i).length + 1)) = 1 := by
  apply Subtype.ext
  change Fin.partialSum (R.blockLengths i) _ / C.boundaryBankLength (coarse.point i) = 1
  have total : Fin.partialSum (R.blockLengths i) (Fin.last ((R.block i).length + 1)) =
      C.boundaryBankLength (coarse.point i) :=
    (fin_partialSum_prefix le_rfl _ _ (fun _ => rfl)).trans (R.block_sum_lengths i)
  rw [total, div_self (C.boundaryBankLength_pos _).ne']

open Classical in
/-- All inserted vertices occur in strict original arclength order. -/
theorem blockParameter_strictMono (i : Fin (n + 1)) : StrictMono (R.blockParameter i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  change Fin.partialSum (R.blockLengths i) k.castSucc /
      C.boundaryBankLength (coarse.point i) <
    Fin.partialSum (R.blockLengths i) k.succ / C.boundaryBankLength (coarse.point i)
  apply (div_lt_div_iff_of_pos_right (C.boundaryBankLength_pos _)).mpr
  rw [Fin.partialSum_succ]
  exact lt_add_of_pos_right _ (E.originalComplex.boundaryBankLength_pos _)

open Classical in
/-- Exact old-edge interpolation of every original and inserted rolled vertex. -/
theorem block_roll_vertex_parameter (i : Fin (n + 1)) (k : Fin ((R.block i).length + 2)) :
    (E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockVertexIndex i k) =
      (C.boundaryChainRoll coarse).point i (R.blockParameter i k) := by
  have product : (R.blockParameter i k).val * C.boundaryBankLength (coarse.point i) =
      Fin.partialSum (R.blockLengths i) k :=
    div_mul_cancel₀ _ (C.boundaryBankLength_pos _).ne'
  rw [R.block_roll_vertex_eq_coarse, PolygonalChain.point, AffineMap.lineMap_apply_module']
  rw [← PolygonalChain.edge, TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, product]
  exact add_comm _ _

open Classical in
/-- Interpolate parameters inside a true fine bank, retaining both endpoints. -/
def pieceParameter (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1))
    (t : unitInterval) : unitInterval :=
  ⟨AffineMap.lineMap (R.blockParameter i k.castSucc).val (R.blockParameter i k.succ).val t.val,
    (convex_Icc (0 : ℝ) 1).lineMap_mem (R.blockParameter i k.castSucc).property
      (R.blockParameter i k.succ).property t.property⟩

open Classical in
/-- Every point on every actual fine rolled bank is its correctly ordered old bank point. -/
theorem block_roll_point (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1))
    (t : unitInterval) :
    (E.originalComplex.boundaryChainRoll R.chain).point (R.blockIndex i k) t =
      (C.boundaryChainRoll coarse).point i (R.pieceParameter i k t) := by
  change AffineMap.lineMap
    ((E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockIndex i k).castSucc)
    ((E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockIndex i k).succ) t.val = _
  rw [← R.blockVertexIndex_castSucc, ← R.blockVertexIndex_succ,
    R.block_roll_vertex_parameter, R.block_roll_vertex_parameter]
  exact ((AffineMap.lineMap ((C.boundaryChainRoll coarse).vertex i.castSucc)
    ((C.boundaryChainRoll coarse).vertex i.succ)).apply_lineMap _ _ _).symm

open Classical in
/-- Every original rolled bank point is attained by a physical fine bank piece. -/
theorem exists_fine_roll_point (i : Fin (n + 1)) (u : unitInterval) :
    ∃ k : Fin ((R.block i).length + 1), ∃ t : unitInterval,
      (E.originalComplex.boundaryChainRoll R.chain).point (R.blockIndex i k) t =
        (C.boundaryChainRoll coarse).point i u := by
  obtain ⟨k, t, at_u⟩ := exists_finite_interpolation (R.blockParameter i)
    (R.blockParameter_zero i) (R.blockParameter_last i) u
  have parameter : R.pieceParameter i k t = u := Subtype.ext at_u
  exact ⟨k, t, (R.block_roll_point i k t).trans (congrArg _ parameter)⟩

open Classical in
/-- The whole refined intrinsic roll has exactly the original planar path image.
This equality permits overlapping developments and preserves every bank endpoint. -/
theorem roll_path_range_eq :
    Set.range (E.originalComplex.boundaryChainRoll R.chain).path =
      Set.range (C.boundaryChainRoll coarse).path := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨j, t, same⟩ := (E.originalComplex.boundaryChainRoll R.chain).path_point_covered
      (by omega) s
    obtain ⟨i, k, at_j⟩ := R.blockIndex_coverage j
    rw [← at_j, R.block_roll_point] at same
    rw [(C.boundaryChainRoll coarse).path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, R.pieceParameter i k t, same.symm⟩)
  · rintro ⟨s, rfl⟩
    obtain ⟨i, u, same⟩ := (C.boundaryChainRoll coarse).path_point_covered (by omega) s
    obtain ⟨k, t, fine⟩ := R.exists_fine_roll_point i u
    rw [(E.originalComplex.boundaryChainRoll R.chain).path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨R.blockIndex i k, t, fine.trans same.symm⟩)

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
