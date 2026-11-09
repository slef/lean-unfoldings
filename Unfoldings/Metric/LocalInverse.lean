module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Homeomorph.Defs

/-! A homeomorphism with isometric neighborhoods has isometric inverse neighborhoods. -/

@[expose] public section

namespace Unfoldings

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

theorem inverse_isometric_neighborhood (H : X ≃ₜ Y) (y : Y)
    (local_isometry : ∃ S : Set X, IsOpen S ∧ H.symm y ∈ S ∧
      Isometry (fun x : S => H x.val)) :
    ∃ T : Set Y, IsOpen T ∧ y ∈ T ∧ Isometry (fun z : T => H.symm z.val) := by
  obtain ⟨S, open_S, inside, isometry⟩ := local_isometry
  let T := H '' S
  have inverse_inside (z : T) : H.symm z.val ∈ S := by
    obtain ⟨x, hx, equal⟩ := z.property
    simpa only [← equal, H.symm_apply_apply] using hx
  let map (z : T) : S := ⟨H.symm z.val, inverse_inside z⟩
  refine ⟨T, H.isOpenMap S open_S, ⟨H.symm y, inside, H.apply_symm_apply y⟩, ?_⟩
  intro a b
  have equal := isometry (map a) (map b)
  change edist (H (H.symm a.val)) (H (H.symm b.val)) =
    edist (H.symm a.val) (H.symm b.val) at equal
  rw [H.apply_symm_apply, H.apply_symm_apply] at equal
  exact equal.symm

end Unfoldings
