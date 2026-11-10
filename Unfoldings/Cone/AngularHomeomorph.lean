module

public import Unfoldings.Cone.AngularMetric
public import Unfoldings.Cone.AngularSector
public import Unfoldings.Cone.SectorChange
public import Unfoldings.Metric.Lipschitz

/-!
# Angular fans admit seam-compatible changes of angles

Cellwise linear changes preserve both boundary-ray parameters. A finite
uniform Lipschitz bound descends them through the actual route metric, and
reverse changes give a continuous inverse. No upper bound on total angle is
required. Compression to a convex quarter-sector supplies a topological model
for interval-link vertex neighborhoods, including overlapping developments.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A B : AngularFan n)

def changeCell (i : Fin (n + 1)) : A.Cell i ≃ₜ B.Cell i :=
  sectorChangeHomeomorph (A.angle i) (B.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'
    (Real.sin_pos_of_pos_of_lt_pi (B.positive i) (B.small i)).ne'

@[simp] theorem changeCell_start (i : Fin (n + 1)) (r : ℝ≥0) :
    A.changeCell B i (A.start i r) = B.start i r := by
  apply Subtype.ext
  have equal := sectorChangeLinearEquiv_combination (A.angle i) (B.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'
    (Real.sin_pos_of_pos_of_lt_pi (B.positive i) (B.small i)).ne' ((r : ℝ), 0)
  change sectorChangeLinearEquiv (A.angle i) (B.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'
    (Real.sin_pos_of_pos_of_lt_pi (B.positive i) (B.small i)).ne' (r : ℂ) = (r : ℂ)
  simpa only [sectorCombination, zero_smul, add_zero] using equal

@[simp] theorem changeCell_finish (i : Fin (n + 1)) (r : ℝ≥0) :
    A.changeCell B i (A.finish i r) = B.finish i r := by
  apply Subtype.ext
  have equal := sectorChangeLinearEquiv_combination (A.angle i) (B.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'
    (Real.sin_pos_of_pos_of_lt_pi (B.positive i) (B.small i)).ne' (0, (r : ℝ))
  change sectorChangeLinearEquiv (A.angle i) (B.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'
    (Real.sin_pos_of_pos_of_lt_pi (B.positive i) (B.small i)).ne'
    ((r : ℝ) • polarRay (A.angle i)) = (r : ℝ) • polarRay (B.angle i)
  simpa only [sectorCombination, Complex.ofReal_zero, zero_add] using equal

@[simp] theorem changeCell_reverse (i : Fin (n + 1)) (x : A.Cell i) :
    B.changeCell A i (A.changeCell B i x) = x :=
  sectorChangeHomeomorph_reverse _ _ _ _ x

def changeBound : ℝ≥0 := 1 + ∑ i, ‖(sectorChangeLinearEquiv (A.angle i) (B.angle i)
    (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne'
    (Real.sin_pos_of_pos_of_lt_pi (B.positive i) (B.small i)).ne').toContinuousLinearMap‖₊

theorem changeBound_pos : 0 < A.changeBound B :=
  lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (by positivity))

theorem changeCell_lipschitz (i : Fin (n + 1)) :
    LipschitzWith (A.changeBound B) (A.changeCell B i) := by
  apply (sectorChangeHomeomorph_lipschitz _ _ _ _).weaken
  exact (Finset.single_le_sum (fun j _ =>
    (show (0 : ℝ≥0) ≤ ‖(sectorChangeLinearEquiv (A.angle j) (B.angle j)
      (Real.sin_pos_of_pos_of_lt_pi (A.positive j) (A.small j)).ne'
      (Real.sin_pos_of_pos_of_lt_pi (B.positive j) (B.small j)).ne').toContinuousLinearMap‖₊
      from zero_le)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)

theorem changeFace_lipschitz (i : Fin (n + 1)) :
    LipschitzWith (A.changeBound B) (B.faceMap i ∘ A.changeCell B i) := by
  simpa only [one_mul] using (B.faceMap_lipschitz i).comp (A.changeCell_lipschitz B i)

theorem changeFace_compatible (a b : MetricGluing.Total A.Cell) (related : A.glue a b) :
    B.faceMap a.1 (A.changeCell B a.1 a.2) = B.faceMap b.1 (A.changeCell B b.1 b.2) := by
  obtain ⟨i, r, rfl, rfl⟩ := related
  rw [A.changeCell_finish, A.changeCell_start]
  exact MetricGluing.point_eq_of_glue B.Cell ⟨i, r, rfl, rfl⟩

def changeAngles : A.Surface → B.Surface :=
  MetricGluing.liftLipschitz A.Cell A.glue (A.changeBound B) (A.changeBound_pos B)
    (fun i => B.faceMap i ∘ A.changeCell B i) (A.changeFace_lipschitz B)
    (A.changeFace_compatible B)

@[simp] theorem changeAngles_faceMap (i : Fin (n + 1)) (x : A.Cell i) :
    A.changeAngles B (A.faceMap i x) = B.faceMap i (A.changeCell B i x) := rfl

theorem changeAngles_lipschitz : LipschitzWith (A.changeBound B) (A.changeAngles B) :=
  MetricGluing.liftLipschitz_lipschitz A.Cell A.glue (A.changeBound B) (A.changeBound_pos B)
    (fun i => B.faceMap i ∘ A.changeCell B i) (A.changeFace_lipschitz B)
    (A.changeFace_compatible B)

@[simp] theorem changeAngles_reverse (z : A.Surface) :
    B.changeAngles A (A.changeAngles B z) = z := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue z
  change B.changeAngles A (A.changeAngles B (A.faceMap i x)) = A.faceMap i x
  rw [A.changeAngles_faceMap, B.changeAngles_faceMap, A.changeCell_reverse]

def changeAnglesHomeomorph : A.Surface ≃ₜ B.Surface where
  toFun := A.changeAngles B
  invFun := B.changeAngles A
  left_inv := A.changeAngles_reverse B
  right_inv := B.changeAngles_reverse A
  continuous_toFun := (A.changeAngles_lipschitz B).continuous
  continuous_invFun := (B.changeAngles_lipschitz A).continuous

@[simp] theorem changeAngles_origin : A.changeAngles B A.origin = B.origin := by
  rw [origin, A.changeAngles_faceMap, A.changeCell_start]
  rfl

theorem angle_le_totalAngle (i : Fin (n + 1)) : A.angle i ≤ A.totalAngle :=
  Finset.single_le_sum (fun j _ => (A.positive j).le) (Finset.mem_univ i)

def compressionFactor : ℝ := (Real.pi / 2) / A.totalAngle

theorem compressionFactor_pos : 0 < A.compressionFactor :=
  div_pos (half_pos Real.pi_pos) A.totalAngle_pos

theorem compressionFactor_mul_total : A.compressionFactor * A.totalAngle = Real.pi / 2 :=
  div_mul_cancel₀ _ A.totalAngle_pos.ne'

def compressedQuarter : AngularFan n where
  angle i := A.compressionFactor * A.angle i
  positive i := mul_pos A.compressionFactor_pos (A.positive i)
  small i := by
    have bound := mul_le_mul_of_nonneg_left (A.angle_le_totalAngle i) A.compressionFactor_pos.le
    rw [A.compressionFactor_mul_total] at bound
    exact bound.trans_lt (by linarith [Real.pi_pos])

theorem compressedQuarter_totalAngle : A.compressedQuarter.totalAngle = Real.pi / 2 := by
  change ∑ i, A.compressionFactor * A.angle i = Real.pi / 2
  rw [← Finset.mul_sum]
  exact A.compressionFactor_mul_total

def quarterSectorHomeomorph : A.Surface ≃ₜ planarSector (Real.pi / 2) :=
  (A.changeAnglesHomeomorph A.compressedQuarter).trans
    ((A.compressedQuarter.sectorIsometry (by
      rw [A.compressedQuarter_totalAngle]
      linarith [Real.pi_pos])).toHomeomorph.trans
        (Homeomorph.setCongr (congrArg planarSector A.compressedQuarter_totalAngle)))

@[simp] theorem quarterSectorHomeomorph_origin :
    (A.quarterSectorHomeomorph A.origin).val = 0 := by
  change A.compressedQuarter.develop (A.changeAngles A.compressedQuarter A.origin) = 0
  rw [A.changeAngles_origin, A.compressedQuarter.develop_origin]

/-- Every slit angular fan is topologically a half-plane, at any total angle. -/
def halfPlaneHomeomorph : A.Surface ≃ₜ PlanarTopology.closedHalfPlane :=
  A.quarterSectorHomeomorph.trans
    (sectorHalfPlaneHomeomorph (Real.pi / 2) (by simp))

@[simp] theorem halfPlaneHomeomorph_origin :
    A.halfPlaneHomeomorph A.origin =
      ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  have center : A.quarterSectorHomeomorph A.origin =
      ⟨0, 0, le_refl 0, 0, le_refl 0, by simp⟩ :=
    Subtype.ext A.quarterSectorHomeomorph_origin
  change sectorHalfPlaneHomeomorph _ _ (A.quarterSectorHomeomorph A.origin) = _
  rw [center, sectorHalfPlaneHomeomorph_zero]

end Unfoldings.AngularFan
