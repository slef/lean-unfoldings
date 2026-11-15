module

public import Mathlib.Topology.MetricSpace.Isometry

/-! Preserve physical maps and named copies through a shared isometric model. -/

@[expose] public section

namespace Unfoldings

variable {X Y Z S : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- Physical identities descend through either direction of a common isometric refinement. -/
theorem map_common_model_isometry (L : Z ≃ᵢ X) (R : Z ≃ᵢ Y)
    (left : X → S) (right : Y → S) (common : Z → S)
    (left_agrees : ∀ z, left (L z) = common z)
    (right_agrees : ∀ z, right (R z) = common z) (x : X) :
    right ((L.symm.trans R) x) = left x :=
  (right_agrees (L.symm x)).trans
    ((left_agrees (L.symm x)).symm.trans (congrArg left (L.apply_symm_apply x)))

/-- Named copies in a common model keep their exact matching original metric copies. -/
theorem common_model_isometry_copy (L : Z ≃ᵢ X) (R : Z ≃ᵢ Y) (z : Z) {x : X} {y : Y}
    (left : L z = x) (right : R z = y) : (L.symm.trans R) x = y :=
  (congrArg (fun x => R (L.symm x)) left).symm.trans
    ((congrArg R (L.symm_apply_apply z)).trans right)

end Unfoldings
