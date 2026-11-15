module

public import Unfoldings.Geometry.SegmentIncidentRays
public import Unfoldings.Geometry.ComplexBankGerm
public import Unfoldings.Geometry.RadialRayVertices

/-! Exact original incoming and outgoing rays at named internal polygonal-bank vertices. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

private theorem point_range_eq_segment (i : Fin n) :
    Set.range (R.chain.point i) =
      segment ℝ (R.chain.vertex i.castSucc) (R.chain.vertex i.succ) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact lineMap_mem_segment ℝ _ _ t.property
  · intro member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, bounds, rfl⟩ := member
    exact ⟨⟨t, bounds⟩, rfl⟩

/-- At a genuine finite bank vertex, all original incident endpoint rays constitute the germ. -/
theorem complexCarrierGerm_eq_incident_rays (nonzero : R.direction ≠ 0) (p : ℂ)
    (not_first : p ≠ R.start) (not_tail : p ∉ Set.range R.tail)
    (not_open : ∀ i : Fin n, p ∉ openSegment ℝ (R.chain.vertex i.castSucc)
      (R.chain.vertex i.succ)) :
    R.complexCarrierGerm p = segmentIncidentRays
      (fun i : Fin n => R.chain.vertex i.castSucc) (fun i => R.chain.vertex i.succ) p := by
  classical
  have carrier_eq : R.carrier = ({R.start} ∪
      (⋃ i : Fin n, segment ℝ (R.chain.vertex i.castSucc) (R.chain.vertex i.succ))) ∪
      Set.range R.tail := by
    rw [carrier, R.chain.path_range]
    simp_rw [R.point_range_eq_segment]
    rfl
  have no_source : ∀ᶠ z in 𝓝 p, z ∉ ({R.start} : Set ℂ) :=
    isClosed_singleton.isOpen_compl.mem_nhds not_first
  have no_tail : ∀ᶠ z in 𝓝 p, z ∉ Set.range R.tail :=
    (R.isClosed_range_tail nonzero).isOpen_compl.mem_nhds not_tail
  have near_segments := eventually_mem_segment_family_iff_incident_rays
    (fun i : Fin n => R.chain.vertex i.castSucc) (fun i => R.chain.vertex i.succ) p not_open
  have near : ∀ᶠ z in 𝓝 p, z ∈ R.carrier ↔ z - p ∈ segmentIncidentRays
      (fun i : Fin n => R.chain.vertex i.castSucc) (fun i => R.chain.vertex i.succ) p := by
    filter_upwards [no_source, no_tail, near_segments] with z first last pieces
    rw [carrier_eq]
    simp only [Set.mem_union, first, last, false_or, or_false, pieces]
  apply eq_of_local_homogeneous_models p
    (fun v _r positive => R.mem_complexCarrierGerm_smul_iff p v positive) _
    (R.eventually_mem_carrier_iff_complexGerm p) near
  intro v r positive
  simp only [segmentIncidentRays, Set.mem_iUnion]
  apply exists_congr
  intro i
  split_ifs <;>
    simp only [Set.mem_union, Set.mem_empty_iff_false, mem_nonnegativeRay_smul_iff _ _ positive]

/-- A named internal vertex of a genuine outward bank has precisely its actual incoming
and outgoing edge rays. Incidence and tail avoidance follow from original radial order. -/
theorem complexCarrierGerm_internal_vertex {m : ℕ} (P : PolygonalRay ℂ (m + 2))
    (outward : P.Outward) (nonzero : P.direction ≠ 0)
    (genuine : ∀ i : Fin (m + 2), P.chain.vertex i.castSucc ≠ P.chain.vertex i.succ)
    (k : Fin (m + 1)) :
    P.complexCarrierGerm (P.chain.vertex k.succ.castSucc) =
      nonnegativeRay (P.chain.vertex k.castSucc.castSucc - P.chain.vertex k.succ.castSucc) ∪
        nonnegativeRay (P.chain.vertex k.succ.succ - P.chain.vertex k.succ.castSucc) := by
  classical
  have injective := P.vertex_injective_of_outward outward genuine
  have not_first : P.chain.vertex k.succ.castSucc ≠ P.start := by
    intro equal
    have indices := injective equal
    have values := congrArg Fin.val indices
    change k.val + 1 = 0 at values
    omega
  have not_tail := P.vertex_not_mem_tail outward genuine nonzero k.succ.castSucc
    (show k.succ.castSucc < Fin.last (m + 2) from by change k.val + 1 < m + 2; omega)
  rw [P.complexCarrierGerm_eq_incident_rays nonzero _ not_first not_tail
    (fun i => P.vertex_not_mem_openSegment outward genuine k.succ.castSucc i)]
  have at_first (i : Fin (m + 2)) :
      P.chain.vertex k.succ.castSucc = P.chain.vertex i.castSucc ↔ i = k.succ := by
    constructor
    · intro equal
      apply Fin.ext
      exact (congrArg Fin.val (injective equal)).symm
    · rintro rfl
      rfl
  have at_last (i : Fin (m + 2)) :
      P.chain.vertex k.succ.castSucc = P.chain.vertex i.succ ↔ i = k.castSucc := by
    constructor
    · intro equal
      apply Fin.ext
      have values := congrArg Fin.val (injective equal)
      change k.val + 1 = i.val + 1 at values
      change i.val = k.val
      omega
    · rintro rfl
      apply congrArg P.chain.vertex
      apply Fin.ext
      rfl
  simp only [segmentIncidentRays]
  simp_rw [at_first, at_last]
  simp [Set.iUnion_union_distrib, Set.iUnion_ite, Set.union_comm]

end Unfoldings.PolygonalRay
