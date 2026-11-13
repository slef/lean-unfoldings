module

public import Unfoldings.Roof.SupportingEnvelope
public import Mathlib.Topology.Order.Lattice

/-! Continuity of the actual supporting-plane roof with arbitrary rim heights. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem continuous_roofHeight : Continuous K.roofHeight := by
  let := K.nonempty_face
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun f _ => (K.supportHeight f).continuous_of_finiteDimensional)

end Unfoldings.ConvexRoof
