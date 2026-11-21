module

public import Unfoldings.FewestNets.FiniteExteriorExample
public import Unfoldings.FewestNets.MeshChartNormals

/-! The first record's exterior margins use actual unit side normals. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeshStar

set_option maxRecDepth 8192 in
-- Both normalizations and all six bisector lengths are checked by the kernel.
theorem q100FirstNormal_unit (i : Fin 6) : ‖q100FirstNormal i‖ = 1 := by
  let d := certificateDenominator
  let h := certificateDenominator_pos
  let c := checkFace h 100 1 1
  let v : CheckedReal d (1 : ℝ) := (CheckedReal.rat d 1).convert (by norm_num)
  let z : CheckedReal d (0 : ℝ) := (CheckedReal.rat d 0).convert (by norm_num)
  let firstAxis := CheckedSpace.vec v z z
  have site : (face 100 1 1).site ≠ 0 :=
    norm_pos_iff.mp (CheckedReal.positive_of_isPositive h (CheckedSpace.norm h c.site)
      (by decide +kernel))
  have chart : bisectorTangent (face 100 1 1).direction (WithLp.toLp 2 ![1, 0, 0]) ≠ 0 :=
    norm_pos_iff.mp (CheckedReal.positive_of_isPositive h
      (CheckedSpace.norm h (Checked.bisectorTangent h (c.direction h) firstAxis))
      (by decide +kernel))
  have side : bisectorTangent (face 100 1 1).direction ((face 100 1 1).neighborDirection i) ≠ 0 :=
    norm_pos_iff.mp (CheckedReal.positive_of_isPositive h
      (CheckedSpace.norm h (Checked.bisectorTangent h (c.direction h) (c.neighborDirection h i)))
      (by fin_cases i <;> decide +kernel))
  exact (face 100 1 1).physicalSideNormal_unit i (NormedSpace.norm_normalize site) chart side

theorem exteriorMargin_q100_face_one_one_checked (i : Fin 6)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (d : Plane)
    (cone : ∀ j : Fin 48,
      0 ≤ inner ℝ
        (AffineMap.lineMap (q100FirstCorner (i - 1)) (q100FirstCorner i) t - q100FirstBody j) d) :
    0.0073243 * ‖d‖ ≤ inner ℝ (q100FirstNormal i) d :=
  exteriorMargin_q100_face_one_one i (q100FirstNormal_unit i) ht d cone

end Unfoldings.FewestNets
