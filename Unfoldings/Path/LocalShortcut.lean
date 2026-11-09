module

public import Unfoldings.Path.Straight
public import Mathlib.Topology.Order.Basic

/-!
# Geodesic avoidance from local strict shortcuts

A nonconstant metric geodesic is injective. If points near a center always
have strict shortcuts relative to their two legs through that center, no
nonconstant geodesic can visit the center at an interior parameter.
-/

@[expose] public section

open Topology
open scoped ENNReal

namespace Path

variable {X : Type*} [EMetricSpace X] {a b : X} {p : Path a b}

theorem IsGeodesic.injective (geodesic : p.IsGeodesic) (distinct : a ≠ b) :
    Function.Injective p := by
  intro s t equal
  have zero : edist a b * edist s t = 0 := by rw [← geodesic s t, equal, edist_self]
  rcases mul_eq_zero.mp zero with endpoints | parameters
  · exact (distinct (edist_eq_zero.mp endpoints)).elim
  · exact edist_eq_zero.mp parameters

/-- Local strict shortcuts are enough; no assumption about which route a
competing shortest path follows is needed. -/
theorem IsGeodesic.ne_of_local_shortcuts (geodesic : p.IsGeodesic) (distinct : a ≠ b)
    (c : X) (r : ℝ≥0∞) (positive : 0 < r)
    (shortcuts : ∀ x ∈ Metric.eball c r, ∀ y ∈ Metric.eball c r,
      x ≠ c → y ≠ c → edist x y < edist x c + edist c y)
    (t : unitInterval) (interior : t ∈ Set.Ioo (0 : unitInterval) 1) : p t ≠ c := by
  intro through
  have near : p ⁻¹' Metric.eball c r ∈ 𝓝 t :=
    (Metric.isOpen_eball.preimage p.continuous).mem_nhds
      (by rw [Set.mem_preimage, through]; exact Metric.mem_eball_self positive)
  obtain ⟨l, h, ⟨lt, th⟩, inside⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0, interior.1⟩ ⟨1, interior.2⟩).mp near
  obtain ⟨s, ls, st⟩ := exists_between lt
  obtain ⟨u, tu, uh⟩ := exists_between th
  have source_ne : p s ≠ c := by
    intro same
    exact st.ne (geodesic.injective distinct (same.trans through.symm))
  have target_ne : p u ≠ c := by
    intro same
    exact tu.ne (geodesic.injective distinct (through.trans same.symm))
  have strict := shortcuts (p s) (inside ⟨ls, st.trans th⟩)
    (p u) (inside ⟨lt.trans tu, uh⟩) source_ne target_ne
  have equal := geodesic.edist_add_edist_eq st.le tu.le
  rw [through] at equal
  exact strict.ne equal.symm

end Path
