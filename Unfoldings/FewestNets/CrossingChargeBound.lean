module

public import Unfoldings.Combinatorics.ComponentEulerAccounting
public import Unfoldings.Geometry.ArcFamilyCrofton

/-! The Crofton bound on the charge of a polygon when crossing witnesses are available. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open MeasureTheory InnerProductGeometry SpatialRotation
open scoped BigOperators

/-- A witness per changed residual side bounds the expected polygon charge.
When three or more sides change, witnesses may be taken from a localized
arc family. Rotations with zero or two changed sides have zero charge. -/
theorem integral_componentCharge_le_of_crossing_witnesses
    {E J : Type*} [Finite E] [DecidableEq E] [Fintype J]
    (s deleted : Finset E) (few : deleted.card ≤ 2)
    (changed : SpatialRotation → E → Prop) [∀ g, DecidablePred (changed g)]
    (u v : ↥(s \ deleted) → Space)
    (frame : J → SpatialRotation) (radius : J → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (not_antipodal : ∀ i, u i + v i ≠ 0)
    (nonneg : ∀ j, 0 ≤ radius j) (small : ∀ j, radius j ≤ Real.pi)
    (integrable : Integrable (fun g => componentCharge (s.filter (changed g)).card) probability)
    (not_one : ∀ᵐ g ∂probability, (s.filter (changed g)).card ≠ 1)
    (witness : ∀ᵐ g ∂probability, 3 ≤ (s.filter (changed g)).card →
      ∀ i : ↥(s \ deleted), changed g i.val →
        ∃ j, g ∈ arcCrossingEvent (u i) (v i) (frame j) (radius j)) :
    (∫ g, componentCharge (s.filter (changed g)).card ∂probability) ≤
      (∑ i, angle (u i) (v i)) * (∑ j, 2 * radius j) / (4 * Real.pi ^ 2) := by
  let : Fintype E := Fintype.ofFinite E
  have each (i : ↥(s \ deleted)) (j : J) (g : SpatialRotation) :
      0 ≤ (arcCrossingEvent (u i) (v i) (frame j) (radius j)).indicator (fun _ => (1 : ℝ)) g := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have pointwise : ∀ᵐ g ∂probability, componentCharge (s.filter (changed g)).card ≤
      (1 / 2 : ℝ) * arcFamilyCrossings u v frame radius g := by
    filter_upwards [not_one, witness] with g hnot hw
    have count_nonneg : 0 ≤ arcFamilyCrossings u v frame radius g :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => each i j g))
    by_cases many : 3 ≤ (s.filter (changed g)).card
    · have residual : (((s \ deleted).filter (changed g)).card : ℝ) ≤
          arcFamilyCrossings u v frame radius g := by
        rw [← Finset.sum_boole]
        change (∑ e ∈ s \ deleted, if changed g e then (1 : ℝ) else 0) ≤ _
        rw [← Finset.sum_attach (s \ deleted)]
        change (∑ e : ↥(s \ deleted), if changed g e.val then (1 : ℝ) else 0) ≤ _
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · obtain ⟨j, hit⟩ := hw many i hi
          have le_sum := Finset.single_le_sum (f := fun k : J =>
            (arcCrossingEvent (u i) (v i) (frame k) (radius k)).indicator (fun _ => (1 : ℝ)) g)
              (fun k _ => each i k g) (Finset.mem_univ j)
          simpa only [Set.indicator_of_mem hit] using le_sum
        · exact Finset.sum_nonneg (fun j _ => each i j g)
      have charge := (componentCharge_le_half_card_filtered_sdiff (changed g) s deleted few hnot).2
      linarith
    · have cases : (s.filter (changed g)).card = 0 ∨ (s.filter (changed g)).card = 2 := by omega
      have nonnegative := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) count_nonneg
      rcases cases with h | h <;> simpa [h, componentCharge] using nonnegative
  have bound := integral_mono_ae integrable
    ((integrable_arcFamilyCrossings u v frame radius hu hv not_antipodal).const_mul (1 / 2))
    pointwise
  rw [integral_const_mul, integral_arcFamilyCrossings u v frame radius
    hu hv not_antipodal nonneg small] at bound
  convert bound using 1 <;> ring

end Unfoldings.FewestNets
