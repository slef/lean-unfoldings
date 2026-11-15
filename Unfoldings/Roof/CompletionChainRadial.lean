module

public import Unfoldings.Roof.CompletionChainRollTrace
public import Unfoldings.Geometry.RadialMarginSubdivision
public import Unfoldings.Geometry.RadialChain

/-! Actual whole bank refinements preserve radial order and the full radial margin constant. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionChainRadialIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Fine-bank interpolation preserves the direction of the original bank parameter. -/
theorem pieceParameter_monotone (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    Monotone (R.pieceParameter i k) := by
  intro t s ordered
  have forward := (R.blockParameter_strictMono i
    (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
  change AffineMap.lineMap (R.blockParameter i k.castSucc).val
      (R.blockParameter i k.succ).val t.val ≤
    AffineMap.lineMap (R.blockParameter i k.castSucc).val (R.blockParameter i k.succ).val s.val
  simp only [AffineMap.lineMap_apply_module', smul_eq_mul]
  change t.val ≤ s.val at ordered
  change (R.blockParameter i k.castSucc).val ≤ (R.blockParameter i k.succ).val at forward
  nlinarith

open Classical in
/-- Every entire fine bank has the radial order of its original rolled bank, including endpoints. -/
theorem roll_radialFrom (source : ℂ)
    (radial : (C.boundaryChainRoll coarse).RadialFrom source 0) :
    (E.originalComplex.boundaryChainRoll R.chain).RadialFrom source 0 := by
  intro j _ t s ordered
  obtain ⟨i, k, at_j⟩ := R.blockIndex_coverage j
  dsimp only
  rw [← at_j, R.block_roll_point, R.block_roll_point]
  exact radial i (Nat.zero_le _) (R.pieceParameter_monotone i k ordered)

open Classical in
/-- The directed fine edge is its positive intrinsic length fraction of the old rolled edge. -/
theorem block_roll_edge_scale (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    (E.originalComplex.boundaryChainRoll R.chain).edge (R.blockIndex i k) =
      (R.blockLengths i k / C.boundaryBankLength (coarse.point i)) •
        (C.boundaryChainRoll coarse).edge i := by
  simp only [TriangleComplex.boundaryChainRoll, PolygonalChain.ofHeadings_edge,
    R.block_heading_eq_coarse, R.blockIndex_point]
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    div_mul_cancel₀ _ (C.boundaryBankLength_pos _).ne']
  rfl

open Classical in
/-- Quantitative radial margins pass to all actual fine rolled banks with no loss in gamma. -/
theorem roll_radial_margin (source : ℂ) {γ : ℝ} (nonnegative : 0 ≤ γ) (small : γ ≤ 1)
    (margin : ∀ i : Fin (n + 1),
      γ * (‖(C.boundaryChainRoll coarse).vertex i.castSucc - source‖ *
        ‖(C.boundaryChainRoll coarse).edge i‖) ≤
      inner ℝ ((C.boundaryChainRoll coarse).vertex i.castSucc - source)
        ((C.boundaryChainRoll coarse).edge i)) :
    ∀ j : Fin (R.length + 1),
      γ * (‖(E.originalComplex.boundaryChainRoll R.chain).vertex j.castSucc - source‖ *
        ‖(E.originalComplex.boundaryChainRoll R.chain).edge j‖) ≤
      inner ℝ ((E.originalComplex.boundaryChainRoll R.chain).vertex j.castSucc - source)
        ((E.originalComplex.boundaryChainRoll R.chain).edge j) := by
  intro j
  obtain ⟨i, k, at_j⟩ := R.blockIndex_coverage j
  have start :
      (E.originalComplex.boundaryChainRoll R.chain).vertex (R.blockIndex i k).castSucc - source =
        ((C.boundaryChainRoll coarse).vertex i.castSucc - source) +
          (R.blockParameter i k.castSucc).val • (C.boundaryChainRoll coarse).edge i := by
    rw [← R.blockVertexIndex_castSucc, R.block_roll_vertex_parameter,
      PolygonalChain.point, AffineMap.lineMap_apply_module', ← PolygonalChain.edge]
    abel
  rw [← at_j, start, R.block_roll_edge_scale]
  exact radial_margin_forward_piece nonnegative small
    (R.blockParameter i k.castSucc).property.1
    (div_nonneg (E.originalComplex.boundaryBankLength_pos _).le
      (C.boundaryBankLength_pos _).le) (margin i)

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
