module

public import Unfoldings.Metric.LocalInverse

/-! Composition and center bounds for constructed isometric neighborhoods. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

theorem compose_isometric_neighborhood (H : X ≃ₜ Y) (K : Y ≃ₜ Z) (x : X)
    (first : ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ Isometry (fun y : S => H y.val))
    (last : ∃ T : Set Y, IsOpen T ∧ H x ∈ T ∧ Isometry (fun y : T => K y.val)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Isometry (fun y : U => (H.trans K) y.val) := by
  obtain ⟨S, open_S, in_S, first_isometry⟩ := first
  obtain ⟨T, open_T, in_T, last_isometry⟩ := last
  let U := S ∩ H ⁻¹' T
  refine ⟨U, open_S.inter (open_T.preimage H.continuous), ⟨in_S, in_T⟩, ?_⟩
  intro a b
  exact (last_isometry ⟨H a.val, a.property.2⟩ ⟨H b.val, b.property.2⟩).trans
    (first_isometry ⟨a.val, a.property.1⟩ ⟨b.val, b.property.1⟩)

theorem center_bound_of_isometric_neighborhood {A B : Type*}
    [PseudoMetricSpace A] [PseudoMetricSpace B] (f : A → B) (x : A)
    (local_isometry : ∃ T : Set A, IsOpen T ∧ x ∈ T ∧ Isometry (fun y : T => f y.val)) :
    ∀ᶠ y in 𝓝 x, dist (f y) (f x) ≤ dist y x := by
  obtain ⟨T, open_T, inside, isometry⟩ := local_isometry
  filter_upwards [open_T.mem_nhds inside] with y hy
  exact (isometry.dist_eq ⟨y, hy⟩ ⟨x, inside⟩).le

end Unfoldings
