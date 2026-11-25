module

public import Unfoldings.FewestNets.LatitudeAnnularFaces
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! The periodically indexed set of sampled latitude sites is a finite spherical set. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real

theorem latitudeSite_add_int_mul_two_pi (row longitude : ℝ) (q : ℤ) :
    latitudeSite row (longitude + q * (2 * π)) = latitudeSite row longitude := by
  unfold latitudeSite
  rw [sin_add_int_mul_two_pi, cos_add_int_mul_two_pi]

/-- Exact periodicity at the repeated meridian. -/
theorem latitudeRowSite_mod (a : ℝ) (j k : ℕ) (positive : 0 < latitudeRowSize a j) :
    latitudeRowSite a j (k % latitudeRowSize a j) = latitudeRowSite a j k := by
  let n := latitudeRowSize a j
  have n_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr positive.ne'
  have sum : (k : ℝ) = (k % n : ℕ) + (n : ℝ) * (k / n : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k n).symm
  have units : rowLongitude n k = rowLongitude n (k % n) + ((k / n : ℕ) : ℝ) * (2 * π) := by
    unfold rowLongitude
    rw [sum]
    field_simp [n_pos]
  change latitudeSite (latitudeColatitude a j) (rowLongitude n (k % n)) =
    latitudeSite (latitudeColatitude a j) (rowLongitude n k)
  rw [units, ← Int.cast_natCast]
  exact (latitudeSite_add_int_mul_two_pi _ _ _).symm

theorem latitudeSites_finite {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    (latitudeSites a).Finite := by
  let I := Σ i : Fin (latitudeStripCount a + 1), Fin (latitudeRowSize a i.val)
  let point (p : I) := latitudeRowSite a p.1.val p.2.val
  apply ((Set.finite_range point).insert (latitudeSite π 0) |>.insert (latitudeSite 0 0)).subset
  intro p hp
  rcases hp with poles | ⟨i, hi, k, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at poles ⊢
    rcases poles with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    have n_pos := latitude_row_size_pos positive small hi
    exact ⟨⟨⟨i, Nat.lt_succ_of_le hi⟩, ⟨k % _, Nat.mod_lt _ n_pos⟩⟩,
      latitudeRowSite_mod a i k n_pos⟩

theorem isCompact_latitudeHull {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    IsCompact (convexHull ℝ (latitudeSites a)) :=
  (latitudeSites_finite positive small).isCompact_convexHull (𝕜 := ℝ)

theorem norm_eq_one_of_mem_latitudeSites {a : ℝ} {p : Space} (mem : p ∈ latitudeSites a) :
    ‖p‖ = 1 := by
  rcases mem with pole | ⟨j, _, k, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at pole
    rcases pole with rfl | rfl <;> exact latitudeSite_unit _ _
  · exact latitudeSite_unit _ _

end Unfoldings.FewestNets
