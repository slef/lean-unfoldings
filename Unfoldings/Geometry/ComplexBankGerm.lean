module

public import Unfoldings.Geometry.PolygonalRayGerm
public import Unfoldings.Geometry.PolygonalRayAffineMap

/-! Exact local direction sets of actual complex polygonal banks, retaining their whole tails. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Use the actual isometric real-plane coordinates of the original complex bank. -/
def planeBank : PolygonalRay Plane n := R.affineMap Complex.orthonormalBasisOneI.repr.toAffineMap

def complexCarrierGerm (x : ℂ) : Set ℂ :=
  Complex.orthonormalBasisOneI.repr ⁻¹'
    (R.planeBank.carrierGerm (Complex.orthonormalBasisOneI.repr x))

theorem mem_planeBank_carrier (z : ℂ) :
    Complex.orthonormalBasisOneI.repr z ∈ R.planeBank.carrier ↔ z ∈ R.carrier := by
  rw [planeBank, affineMap_carrier]
  constructor
  · rintro ⟨w, member, equal⟩
    have same : w = z := Complex.orthonormalBasisOneI.repr.injective equal
    exact same ▸ member
  · intro member
    exact ⟨z, member, rfl⟩

/-- The local bank directions are constructed from its original finite segments and tail. -/
theorem eventually_mem_carrier_iff_complexGerm (x : ℂ) :
    ∀ᶠ z in 𝓝 x, z ∈ R.carrier ↔ z - x ∈ R.complexCarrierGerm x := by
  have near := R.planeBank.eventually_mem_carrier_iff_germ (Complex.orthonormalBasisOneI.repr x)
  filter_upwards [Complex.orthonormalBasisOneI.repr.continuous.continuousAt.tendsto.eventually near]
    with z hz
  rw [R.mem_planeBank_carrier] at hz
  simpa only [complexCarrierGerm, Set.mem_preimage, map_sub] using hz

theorem mem_complexCarrierGerm_smul_iff (x v : ℂ) {r : ℝ} (positive : 0 < r) :
    r • v ∈ R.complexCarrierGerm x ↔ v ∈ R.complexCarrierGerm x := by
  simp only [complexCarrierGerm, Set.mem_preimage, map_smul,
    mem_carrierGerm_smul_iff _ _ _ positive]

/-- Inactive original bank pieces contribute no artificial zero direction. -/
theorem zero_mem_complexCarrierGerm_iff (x : ℂ) :
    (0 : ℂ) ∈ R.complexCarrierGerm x ↔ x ∈ R.carrier := by
  simp only [complexCarrierGerm, Set.mem_preimage, map_zero, zero_mem_carrierGerm_iff,
    mem_planeBank_carrier]

/-- A bank absent from a physical point contributes no directions to its local cone. -/
theorem complexCarrierGerm_eq_empty_iff (x : ℂ) :
    R.complexCarrierGerm x = ∅ ↔ x ∉ R.carrier := by
  constructor
  · intro empty member
    have zero := (R.zero_mem_complexCarrierGerm_iff x).mpr member
    simp only [empty, Set.mem_empty_iff_false] at zero
  · intro outside
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v member
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    have not_incident : Complex.orthonormalBasisOneI.repr x ∉
        AffineArrangement.closedChamber (R.planeBank.carrierInequalities i) (fun _ => true) := by
      intro incident
      apply outside
      apply (R.mem_planeBank_carrier x).mp
      rw [R.planeBank.carrier_eq_iUnion_closedChamber]
      exact Set.mem_iUnion.mpr ⟨i, incident⟩
    simp only [AffineArrangement.cellGerm, ite_eq_right not_incident,
      Set.mem_empty_iff_false] at hi

end Unfoldings.PolygonalRay
