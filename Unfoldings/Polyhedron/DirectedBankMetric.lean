module

public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Polyhedron.BankLengths
public import Unfoldings.Metric.HalfOpenIntervalExtension

/-! Exact metric speed and spatial placement of every original directed finite bank. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

@[simp] theorem toSpace_bankMap (bank : C.BoundaryBank retain)
    (q : (C.triangle bank.val.face).Edge bank.val.edge) :
    F.toSpace retain (C.bankMap retain bank q) = F.place bank.val.face q.val := by
  rw [TriangleComplex.bankMap, Function.comp_apply, F.toSpace_faceMap]
  rfl

/-- Every two points on one original finite bank have their full spatial distance. -/
theorem edist_directedBoundaryPath_eq_spatial (p : C.BoundaryEnd retain) (s t : unitInterval) :
    edist (C.directedBoundaryPath p s) (C.directedBoundaryPath p t) =
      edist (F.toSpace retain (C.directedBoundaryPath p s))
        (F.toSpace retain (C.directedBoundaryPath p t)) := by
  let bank := (C.boundaryEndEquiv retain p).1
  let flag := (C.boundaryEndEquiv retain p).2
  let first := (C.triangle bank.val.face).edgeMap bank.val.edge
    (C.bankParameterFromEnd bank flag s)
  let last := (C.triangle bank.val.face).edgeMap bank.val.edge
    (C.bankParameterFromEnd bank flag t)
  exact ((F.faceMap_isometry retain bank.val.face).edist_eq first last).trans
    ((F.face_isometry bank.val.face).edist_eq first last).symm

/-- The spatial copy of the entire original directed bank has its exact original speed. -/
def directedBankSpatialDilation (p : C.BoundaryEnd retain) : unitInterval →ᵈ Space where
  toFun t := F.toSpace retain (C.directedBoundaryPath p t)
  edist_eq' := ⟨‖F.germDirection p.val‖₊,
    nnnorm_ne_zero_iff.mpr (F.germDirection_ne_zero p.val), by
    intro s t
    rw [F.directedBoundaryPath_position, F.directedBoundaryPath_position, edist_dist, edist_dist]
    change ENNReal.ofReal (dist
      (F.boundaryPosition p + s.val • F.germDirection p.val)
      (F.boundaryPosition p + t.val • F.germDirection p.val)) =
      (‖F.germDirection p.val‖₊ : ℝ≥0∞) * ENNReal.ofReal (dist s.val t.val)
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
      Real.dist_eq, ENNReal.ofReal_mul (abs_nonneg _), mul_comm, ofReal_norm, enorm_eq_nnnorm]⟩

/-- The original intrinsic bank itself is a closed interval dilation, allowing distant
banks and faces to overlap in any separate planar development. -/
def directedBankDilation (p : C.BoundaryEnd retain) : unitInterval →ᵈ C.Realization retain :=
  dilationOfIsometricLift (F.directedBankSpatialDilation p) id isometry_id
    (C.directedBoundaryPath p) (F.edist_directedBoundaryPath_eq_spatial p)

@[simp] theorem directedBankDilation_apply (p : C.BoundaryEnd retain) (t : unitInterval) :
    F.directedBankDilation p t = C.directedBoundaryPath p t := rfl

end Unfoldings.SpatialFolding
