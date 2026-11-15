module

public import Unfoldings.Geometry.PolygonalBankVertexGerm
public import Unfoldings.Geometry.RadialVertexCoordinates

/-! The final finite bank vertex retains its incoming edge and its true unbounded tail ray. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings.PolygonalChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (P : PolygonalChain E n)

/-- The original carrier is exactly its source and entire closed finite segments. -/
theorem path_range_eq_segments : Set.range P.path = {P.vertex 0} ∪
    ⋃ i : Fin n, segment ℝ (P.vertex i.castSucc) (P.vertex i.succ) := by
  rw [P.path_range]
  congr 1
  apply Set.iUnion_congr
  intro i
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact lineMap_mem_segment ℝ _ _ t.property
  · intro member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, bounds, equal⟩ := member
    exact ⟨⟨t, bounds⟩, equal⟩

end Unfoldings.PolygonalChain

namespace Unfoldings.PolygonalRay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (R : PolygonalRay E n)

/-- The true whole tail is exactly the translated original outgoing ray. -/
theorem mem_range_tail_iff_ray (z : E) : z ∈ Set.range R.tail ↔
    z - R.chain.vertex (Fin.last n) ∈ nonnegativeRay R.direction := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.coe_nonneg, by simp only [tail, add_sub_cancel_left]⟩
  · rintro ⟨t, nonnegative, equal⟩
    refine ⟨⟨t, nonnegative⟩, ?_⟩
    change R.chain.vertex (Fin.last n) + t • R.direction = z
    rw [← equal, add_sub_cancel]

/-- At the original last vertex the bank germ includes the actual infinite tail, rather
than a parallel replacement or a truncated segment. -/
theorem complexCarrierGerm_terminal_vertex {m : ℕ} (P : PolygonalRay ℂ (m + 1))
    (outward : P.Outward)
    (genuine : ∀ i : Fin (m + 1), P.chain.vertex i.castSucc ≠ P.chain.vertex i.succ) :
    P.complexCarrierGerm (P.chain.vertex (Fin.last (m + 1))) =
      nonnegativeRay (P.chain.vertex (Fin.last m).castSucc -
        P.chain.vertex (Fin.last (m + 1))) ∪ nonnegativeRay P.direction := by
  classical
  let p := P.chain.vertex (Fin.last (m + 1))
  have injective := P.vertex_injective_of_outward outward genuine
  have not_first : p ≠ P.start := by
    intro equal
    have values := congrArg Fin.val (injective equal)
    change m + 1 = 0 at values
    omega
  have at_first (i : Fin (m + 1)) : p ≠ P.chain.vertex i.castSucc := by
    intro equal
    have values := congrArg Fin.val (injective equal)
    change m + 1 = i.val at values
    omega
  have at_last (i : Fin (m + 1)) : p = P.chain.vertex i.succ ↔ i = Fin.last m := by
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val (injective equal)
      change m + 1 = i.val + 1 at values
      change i.val = m
      omega
    · rintro rfl
      rfl
  have incident : segmentIncidentRays (fun i : Fin (m + 1) => P.chain.vertex i.castSucc)
      (fun i => P.chain.vertex i.succ) p =
        nonnegativeRay (P.chain.vertex (Fin.last m).castSucc - p) := by
    simp only [segmentIncidentRays]
    simp_rw [ite_eq_right (at_first _), at_last]
    simp [Set.iUnion_ite]
  have near_segments := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin (m + 1) => P.chain.vertex i.castSucc) (fun i => P.chain.vertex i.succ) p
    (fun i => P.vertex_not_mem_openSegment outward genuine (Fin.last (m + 1)) i)
  rw [incident] at near_segments
  have no_source : ∀ᶠ z in 𝓝 p, z ∉ ({P.start} : Set ℂ) :=
    isClosed_singleton.isOpen_compl.mem_nhds not_first
  have near : ∀ᶠ z in 𝓝 p, z ∈ P.carrier ↔
      z - p ∈ nonnegativeRay (P.chain.vertex (Fin.last m).castSucc - p) ∪
        nonnegativeRay P.direction := by
    filter_upwards [near_segments, no_source] with z segments first
    rw [carrier, P.chain.path_range_eq_segments]
    change z ∉ ({P.chain.vertex 0} : Set ℂ) at first
    simp only [Set.mem_union, P.mem_range_tail_iff_ray, first, false_or, segments]
    rfl
  apply eq_of_local_homogeneous_models p
    (fun v _r positive => P.mem_complexCarrierGerm_smul_iff p v positive) _
    (P.eventually_mem_carrier_iff_complexGerm p) near
  intro v r positive
  simp only [Set.mem_union, mem_nonnegativeRay_smul_iff _ _ positive]

end Unfoldings.PolygonalRay
