module

public import Unfoldings.Roof.AboveGraphBankEnds
public import Unfoldings.Roof.RestrictedBankRays
public import Unfoldings.Roof.SharpClosingContacts

/-! The straight links of an aligned closing graph carry literal restricted roof turns. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
  (sample : Face → Plane) (sample_in : ∀ i, sample i ∈ interior (K.projectedTriangle i).carrier)
  (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
  (aligned : ∀ i, Disjoint (interior (K.projectedTriangle i).carrier) (graphPoint f '' Set.Icc a b))

local notation "Above" => facesAboveGraph sample f a b

include hf sample_in endpoints aligned in
set_option maxHeartbeats 1200000 in
open Classical in
/-- Select regular straight contacts from the actual graph. The bound on their
angle excess will use the actual restricted fan, even where the graph crosses a crease. -/
theorem exists_regularClosingLink_facesAboveGraph {I : Type*}
    (origin direction : Plane) (genuine : direction ≠ 0)
    (contact : I → C.Vertex Set.univ) (injective : Function.Injective contact)
    (time : I → ℝ) (at_time : ∀ i, K.projectedVertex (contact i) = origin + time i • direction)
    (inside : ∀ i, K.projectedVertex (contact i) ∈ interior K.footprint)
    (window : ∀ i, K.projectedVertex (contact i) 0 ∈ Set.Ioo a b)
    (on_graph : ∀ i, K.projectedVertex (contact i) 1 = f (K.projectedVertex (contact i) 0))
    (locally_line : ∀ i, ∀ᶠ z in 𝓝 (K.projectedVertex (contact i)),
      z 0 ∈ Set.Ioo a b → z 1 = f (z 0) → ∃ t : ℝ, z = origin + t • direction)
    (regular : ∀ i, K.HasRegularSectionSlopes (contact i) direction) :
    ∃ L : K.RegularClosingLink Above origin direction I,
      L.time = time ∧
      ∀ i, K.restrictedBoundaryTurnError Above (L.bank i) =
        -K.regionalAngleExcess Above (contact i) := by
  choose bank original position turn using
    fun i => K.exists_boundaryEnd_facesAboveGraph hf sample sample_in endpoints aligned
      (contact i) (inside i) (window i) (on_graph i)
  have straight (i : I) :
      ∀ᶠ z in 𝓝 (Cap.horizontal ((K.folding.restrictFaces Above).boundaryPosition (bank i))),
        z ∈ frontier (K.restrictedCarrier Above) →
        ∃ s : ℝ, z = Cap.horizontal ((K.folding.restrictFaces Above).boundaryPosition (bank i)) +
          s • direction := by
    rw [position]
    let x := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0
    filter_upwards [locally_line i, isOpen_interior.mem_nhds (inside i),
      (isOpen_Ioo.preimage x.continuous).mem_nhds (window i)] with z local_line in_roof in_window
    intro bank_member
    have on_graph := K.eq_graph_of_mem_frontier_facesAboveGraph hf sample sample_in endpoints aligned
      in_roof in_window bank_member
    obtain ⟨s, location⟩ := local_line in_window on_graph
    exact ⟨s - time i, by rw [location, at_time i]; module⟩
  choose first last opposite outgoing incoming using
    fun i => K.restricted_bank_rays_of_local_line Above (bank i) direction genuine (straight i)
  have distinct : Function.Injective time := by
    intro i j equal
    apply injective
    apply K.projectedVertex_injective
    rw [at_time i, at_time j, equal]
  refine ⟨⟨bank, time, distinct, fun i => (position i).trans (at_time i), ?_,
    first, last, opposite, outgoing, incoming, ?_⟩, rfl, turn⟩
  · intro i
    rw [← at_time i]
    exact inside i
  · intro i
    rw [original i]
    exact regular i

end Unfoldings.ConvexRoof
