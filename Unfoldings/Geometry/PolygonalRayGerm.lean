module

public import Unfoldings.Geometry.PolygonalRayInequalities
public import Unfoldings.Geometry.AffineArrangementGerm

/-! Exact local direction sets and retained-attachment tests for actual polygonal ray cuts. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay Plane n)

/-- The actual union of incident edge and tail tangent cones at a physical point. -/
def carrierGerm (x : Plane) : Set Plane :=
  ⋃ i, AffineArrangement.cellGerm (R.carrierInequalities i) (fun _ => true) x

theorem mem_carrierGerm_smul_iff (x v : Plane) {t : ℝ} (positive : 0 < t) :
    t • v ∈ R.carrierGerm x ↔ v ∈ R.carrierGerm x := by
  simp only [carrierGerm, Set.mem_iUnion,
    AffineArrangement.mem_cellGerm_smul_iff _ _ _ _ positive]

/-- No simplicity or nonzero-edge assumption is needed for the exact local cut germ. -/
theorem eventually_mem_carrier_iff_germ (x : Plane) :
    ∀ᶠ z in 𝓝 x, z ∈ R.carrier ↔ z - x ∈ R.carrierGerm x := by
  have near : ∀ᶠ z in 𝓝 x, ∀ i,
      z ∈ AffineArrangement.closedChamber (R.carrierInequalities i) (fun _ => true) ↔
        z - x ∈ AffineArrangement.cellGerm (R.carrierInequalities i) (fun _ => true) x :=
    eventually_all.mpr (fun i =>
      AffineArrangement.eventually_mem_closedChamber_iff_cellGerm
        (R.carrierInequalities i) (fun _ => true) x)
  filter_upwards [near] with z hz
  simp only [R.carrier_eq_iUnion_closedChamber, carrierGerm, Set.mem_iUnion, hz]

theorem zero_mem_carrierGerm_iff (x : Plane) : (0 : Plane) ∈ R.carrierGerm x ↔ x ∈ R.carrier := by
  have each (i : Unit ⊕ (Fin n ⊕ Unit)) :
      (0 : Plane) ∈ AffineArrangement.cellGerm (R.carrierInequalities i) (fun _ => true) x ↔
        x ∈ AffineArrangement.closedChamber (R.carrierInequalities i) (fun _ => true) := by
    classical
    by_cases member : x ∈ AffineArrangement.closedChamber (R.carrierInequalities i) (fun _ => true)
    · simp [AffineArrangement.cellGerm, member, AffineArrangement.zero_mem_tangentCell]
    · simp [AffineArrangement.cellGerm, member]
  simp only [carrierGerm, R.carrier_eq_iUnion_closedChamber, Set.mem_iUnion, each]

/-- Degenerate finite edges and a zero terminal direction still give a closed actual carrier. -/
theorem isClosed_carrier_without_direction : IsClosed R.carrier := by
  rw [R.carrier_eq_iUnion_closedChamber]
  exact isClosed_iUnion_of_finite (fun i => AffineArrangement.isClosed_closedChamber
    (R.carrierInequalities i) (fun _ => true))

variable {K : Type*} [Finite K] {length : K → ℕ} (rays : ∀ k, PolygonalRay Plane (length k))

/-- The actual finite affine pieces of a possibly branching family of polygonal cuts. -/
def familyCarrierInequalities : (Σ k, Unit ⊕ (Fin (length k) ⊕ Unit)) →
    Fin 6 → Plane →ᵃ[ℝ] ℝ := fun i => (rays i.1).carrierInequalities i.2

omit [Finite K] in
theorem family_carrier_eq_iUnion_closedChamber :
    (⋃ k, (rays k).carrier) = ⋃ i,
      AffineArrangement.closedChamber (familyCarrierInequalities rays i) (fun _ => true) := by
  rw [Set.iUnion_sigma]
  congr 1
  funext k
  exact (rays k).carrier_eq_iUnion_closedChamber

/-- The geometric retained-attachment test applies directly to original polygonal cut rays. -/
theorem mem_closure_family_attachment_iff {I J : Type*} [Finite I] [Finite J]
    (f : I → Plane →ᵃ[ℝ] ℝ) (signs : I → Bool)
    (g : J → Plane →ᵃ[ℝ] ℝ) (otherSigns : J → Bool) (x : Plane) :
    x ∈ closure ((AffineArrangement.closedChamber f signs ∩
      AffineArrangement.closedChamber g otherSigns) \ (⋃ k, (rays k).carrier)) ↔
      ((AffineArrangement.cellGerm f signs x ∩ AffineArrangement.cellGerm g otherSigns x) \
        (⋃ k, (rays k).carrierGerm x)).Nonempty := by
  have result := AffineArrangement.mem_closure_attachment_iff f signs g otherSigns
    (familyCarrierInequalities rays) (fun _ _ => true) x
  rw [← family_carrier_eq_iUnion_closedChamber rays] at result
  have germs : (⋃ i, AffineArrangement.cellGerm
      (familyCarrierInequalities rays i) (fun _ => true) x) =
        ⋃ k, (rays k).carrierGerm x := by
    rw [Set.iUnion_sigma]
    rfl
  rwa [germs] at result

/-- At an actual cut point, retained attachments are detected exactly
on the unit direction circle. -/
theorem mem_closure_family_attachment_iff_unit {I J : Type*} [Finite I] [Finite J]
    (f : I → Plane →ᵃ[ℝ] ℝ) (signs : I → Bool)
    (g : J → Plane →ᵃ[ℝ] ℝ) (otherSigns : J → Bool) (x : Plane)
    (on_cut : x ∈ ⋃ k, (rays k).carrier) :
    x ∈ closure ((AffineArrangement.closedChamber f signs ∩
      AffineArrangement.closedChamber g otherSigns) \ (⋃ k, (rays k).carrier)) ↔
      ∃ v : Plane, ‖v‖ = 1 ∧ v ∈
        ((AffineArrangement.cellGerm f signs x ∩ AffineArrangement.cellGerm g otherSigns x) \
          (⋃ k, (rays k).carrierGerm x)) := by
  rw [mem_closure_family_attachment_iff rays f signs g otherSigns x]
  constructor
  · rintro ⟨v, hv⟩
    have zero_cut : (0 : Plane) ∈ ⋃ k, (rays k).carrierGerm x := by
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp on_cut
      exact Set.mem_iUnion.mpr ⟨k, ((rays k).zero_mem_carrierGerm_iff x).mpr hk⟩
    have nonzero : v ≠ 0 := by
      intro zero
      exact hv.2 (zero ▸ zero_cut)
    have positive : 0 < ‖v‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr nonzero)
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg positive.le,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]
    · simpa only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion,
        AffineArrangement.mem_cellGerm_smul_iff _ _ _ _ positive,
        mem_carrierGerm_smul_iff _ _ _ positive] using hv
  · rintro ⟨v, _unit, hv⟩
    exact ⟨v, hv⟩

end Unfoldings.PolygonalRay
