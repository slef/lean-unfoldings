module

public import Unfoldings.Geometry.GraphRegionSides
public import Mathlib.Analysis.Convex.Topology

/-! Classify an aligned triangle by its interior within a graph window, even if it straddles an end line. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

open Filter Topology

/-- A region is on the upper side in the open graph window when its interior
meets that side there. Faces away from the window have no contribution. -/
def interiorAboveGraph (f : ℝ → ℝ) (a b : ℝ) (S : Set Plane) : Prop :=
  ∃ z ∈ interior S, z 0 ∈ Set.Ioo a b ∧ f (z 0) < z 1

/-- In a convex aligned region one interior point in the open window
determines the side throughout its intersection with the window. -/
theorem interiorAboveGraph_iff_of_mem_window {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    {S : Set Plane} (convex : Convex ℝ S)
    (aligned : Disjoint (interior S) (graphPoint f '' Set.Icc a b))
    {z : Plane} (member : z ∈ interior S) (window : z 0 ∈ Set.Ioo a b) :
    interiorAboveGraph f a b S ↔ f (z 0) < z 1 := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  let U := interior S ∩ x ⁻¹' Set.Ioo a b
  have connected : IsPreconnected U :=
    (convex.interior.inter ((convex_Ioo a b).linear_preimage x.toLinearMap)).isPreconnected
  constructor
  · rintro ⟨p, inside, time, higher⟩
    exact ((aboveGraph_iff_of_cell hf connected (fun v (h : v ∈ U) => ⟨h.2.1.ne', h.2.2.ne⟩)
      (aligned.mono_left Set.inter_subset_left) (show p ∈ U from ⟨inside, time⟩)
      (show z ∈ U from ⟨member, window⟩)).mp ⟨time, higher⟩).2
  · exact fun above => ⟨z, member, window, above⟩

/-- Interior points of a genuine closed convex face approach each of its
boundary points within any open horizontal window containing that point. -/
theorem exists_interior_mem_window_of_mem_face {S : Set Plane} (convex : Convex ℝ S)
    (nonempty : (interior S).Nonempty) {a b : ℝ} {z : Plane}
    (member : z ∈ S) (window : z 0 ∈ Set.Ioo a b) :
    ∃ p ∈ interior S, p 0 ∈ Set.Ioo a b := by
  let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
  have near : x ⁻¹' Set.Ioo a b ∈ 𝓝 z := (isOpen_Ioo.preimage x.continuous).mem_nhds window
  have closed : z ∈ closure (interior S) := by
    rw [convex.closure_interior_eq_closure_of_nonempty_interior nonempty]
    exact subset_closure member
  obtain ⟨p, hp, inside⟩ := mem_closure_iff_nhds.mp closed _ near
  exact ⟨p, inside, hp⟩

/-- Any refined face that reaches the open graph window lies on the same
side there as its aligned original parent. -/
theorem interiorAboveGraph_eq_of_nested {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    {S T : Set Plane} (convex_S : Convex ℝ S) (convex_T : Convex ℝ T)
    (nonempty : (interior S).Nonempty) (nested : S ⊆ T)
    (aligned : Disjoint (interior T) (graphPoint f '' Set.Icc a b))
    {z : Plane} (member : z ∈ S) (window : z 0 ∈ Set.Ioo a b) :
    interiorAboveGraph f a b S ↔ interiorAboveGraph f a b T := by
  obtain ⟨p, hp, time⟩ := exists_interior_mem_window_of_mem_face convex_S nonempty member window
  exact (interiorAboveGraph_iff_of_mem_window hf convex_S (aligned.mono_left (interior_mono nested))
      hp time).trans
    (interiorAboveGraph_iff_of_mem_window hf convex_T aligned (interior_mono nested hp) time).symm

end Unfoldings.PlanarTopology
