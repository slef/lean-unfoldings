module

public import Unfoldings.Geometry.CyclicSeparatedHeadings
public import Unfoldings.Geometry.StereographicTwoSide
public import Unfoldings.Geometry.StereographicFrameInvariance

/-! Apply the two-side perimeter estimate to an actual positively oriented chart cycle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open InnerProductGeometry MeasureTheory
open scoped BigOperators
attribute [local instance] Complex.finrank_real_complex_fact

/-- A positively oriented framed chord cycle with turns bounded below
satisfies the stereographic two-side bound with its original cyclic indices. -/
theorem exists_omit_two_cyclic_spherical_chords_of_small_minimum {K : Set Plane}
    (compact : IsCompact K) (convex : Convex ℝ K) (disk : ∀ x ∈ K, ‖x‖ ≤ 1)
    {a b : Plane} (ha : a ∈ K) (hb : b ∈ K) {d : ℝ} (nonneg : 0 ≤ d)
    (diameter : d ≤ 2 * dist a b) (T : Plane ≃ₗᵢ[ℝ] Plane) (base : T a 1 = T b 1)
    {n : ℕ} (p : Fin (n + 1) → Plane) (points : ∀ i, p i ∈ K)
    (injective : Function.Injective p) {eta : ℝ} (eta_pos : 0 < eta) (eta_small : eta ≤ Real.pi / 2)
    (minimum : ∀ i,
      eta ≤ angle (p (finRotate (n + 1) i) - p i)
        (p (finRotate (n + 1) (finRotate (n + 1) i)) - p (finRotate (n + 1) i)))
    (support : let q := Complex.orthonormalBasisOneI.repr.symm ∘ T ∘ p
      ∀ i j, 0 ≤ Complex.orientation.areaForm (q (finRotate (n + 1) i) - q i) (q j - q i))
    (positive : let q := Complex.orthonormalBasisOneI.repr.symm ∘ T ∘ p
      ∀ i, 0 < Complex.orientation.areaForm (q (finRotate (n + 1) i) - q i)
        (q (finRotate (n + 1) (finRotate (n + 1) i)) - q (finRotate (n + 1) i))) :
    ∃ omitted : Finset (Fin (n + 1)), omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.univ \ omitted,
        angle (inverseStereographic (p i)) (inverseStereographic (p (finRotate (n + 1) i)))) *
        d * Real.sin eta ≤ 16 * (volume : Measure Plane).real K := by
  classical
  let L := T.trans Complex.orthonormalBasisOneI.repr.symm
  let q := L ∘ p
  let next := finRotate (n + 1)
  let ray (i : Fin (n + 1)) := q (next i) - q i
  have total : (∑ i, angle (ray i) (ray (next i))) = 2 * Real.pi :=
    sum_convex_chord_turns_eq_two_pi q (L.injective.comp injective) support positive
  have lower (i : Fin (n + 1)) : eta ≤ angle (ray i) (ray (next i)) := by
    change eta ≤ angle (L (p (next i)) - L (p i))
      (L (p (next (next i))) - L (p (next i)))
    rw [← L.map_sub, ← L.map_sub]
    calc
      eta ≤ angle (p (next i) - p i) (p (next (next i)) - p (next i)) := minimum i
      _ = _ := (L.toLinearIsometry.angle_map _ _).symm
  obtain ⟨start, head, head_range, gaps, rays⟩ :=
    exists_separated_cyclic_ray_headings ray eta_pos lower positive total
  let shift (i : Fin (n + 1)) := i + start
  let index (i : ℕ) : Fin (n + 1) := ⟨i % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  let path (i : ℕ) := T (p (shift (index i)))
  let heading (i : ℕ) := head (index i)
  let K' := T '' K
  have index_val (i : Fin (n + 1)) : index i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have index_next (i : ℕ) : index (i + 1) = next (index i) := by
    apply Fin.ext
    rw [finRotate_apply, Fin.val_add, Fin.val_one']
    exact Nat.add_mod _ _ _
  have closed : path (n + 1) = path 0 := by
    have eq : index (n + 1) = index 0 := Fin.ext (by simp [index])
    simp only [path, eq]
  have vertical (i : ℕ) :
      path (i + 1) 1 - path i 1 = dist (path i) (path (i + 1)) * Real.sin (heading i) := by
    have route := rays (index i)
    have upcoming : shift (index (i + 1)) = next (shift (index i)) := by
      rw [index_next]
      exact add_finRotate_comm (index i) start
    have ray' : ray (shift (index i)) =
        Complex.orthonormalBasisOneI.repr.symm (path (i + 1) - path i) := by
      rw [map_sub]
      change q (next (shift (index i))) - q (shift (index i)) =
        q (shift (index (i + 1))) - q (shift (index i))
      rw [upcoming]
    change ray (shift (index i)) = (‖ray (shift (index i))‖ : ℂ) * polarRay (heading i) at route
    rw [ray', LinearIsometryEquiv.norm_map] at route
    have im := congrArg Complex.im route
    rw [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, polarRay_im] at im
    rw [dist_comm, dist_eq_norm]
    simpa [Complex.add_im, Complex.mul_im, PiLp.sub_apply] using im
  have framed_compact : IsCompact K' := compact.image T.continuous
  have framed_convex : Convex ℝ K' := convex.linear_image (T.toLinearEquiv : Plane →ₗ[ℝ] Plane)
  have framed_disk : ∀ x ∈ K', ‖x‖ ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [T.norm_map]
    exact disk x hx
  have gap_nat (i j : ℕ) (ij : i < j) (jn : j < n + 1) :
      eta ≤ heading j - heading i ∧ heading j - heading i ≤ 2 * Real.pi - eta := by
    apply gaps
    change i % (n + 1) < j % (n + 1)
    rwa [Nat.mod_eq_of_lt (ij.trans jn), Nat.mod_eq_of_lt jn]
  obtain ⟨del, subset, few, bound⟩ := exists_omit_two_spherical_chords_of_small_minimum
    framed_compact framed_convex framed_disk (Set.mem_image_of_mem T ha) (Set.mem_image_of_mem T hb)
    base nonneg (by rwa [T.dist_map]) (n + 1) path heading
    (fun i _ => Set.mem_image_of_mem T (points (shift (index i)))) closed eta_pos eta_small
    (fun i _ => ⟨(head_range (index i)).1, (head_range (index i)).2.le⟩) gap_nat
    (fun i _ => vertical i)
  let delFin : Finset (Fin (n + 1)) := Finset.univ.filter fun i => i.val ∈ del
  have map_val_del : delFin.map Fin.valEmbedding = del := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      exact (Finset.mem_filter.mp hi).2
    · intro hj
      let i : Fin (n + 1) := ⟨j, Finset.mem_range.mp (subset hj)⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  have remaining :
      (Finset.univ \ delFin).map Fin.valEmbedding = Finset.range (n + 1) \ del := by
    rw [Finset.map_sdiff, Fin.map_valEmbedding_univ, Nat.Iio_eq_range, map_val_del]
  let shifted : Fin (n + 1) ↪ Fin (n + 1) := ⟨shift, fun _ _ equal => add_right_cancel equal⟩
  let removed := delFin.map shifted
  have map_all : (Finset.univ : Finset (Fin (n + 1))).map shifted = Finset.univ := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
    exact ⟨j - start, sub_add_cancel _ _⟩
  have map_remain : (Finset.univ \ delFin).map shifted = Finset.univ \ removed := by
    rw [Finset.map_sdiff, map_all]
  have few_fin : removed.card ≤ 2 := by
    have eq := congrArg Finset.card map_val_del
    rw [Finset.card_map] at eq
    simpa only [removed, Finset.card_map, eq] using few
  have framed_angle (i : Fin (n + 1)) :
      angle (inverseStereographic (path i.val)) (inverseStereographic (path (i.val + 1))) =
        angle (inverseStereographic (p (shift i))) (inverseStereographic (p (next (shift i)))) := by
    rw [show path i.val = T (p (shift (index i.val))) from rfl,
      show path (i.val + 1) = T (p (shift (index (i.val + 1)))) from rfl,
      index_next, index_val, show shift (next i) = next (shift i) from add_finRotate_comm i start]
    exact angle_inverseStereographic_isometry T _ _
  have area_eq : (volume : Measure Plane).real K' = (volume : Measure Plane).real K :=
    congrArg ENNReal.toReal (volume_linearIsometryEquiv_image T compact)
  refine ⟨removed, few_fin, ?_⟩
  rw [← map_remain, Finset.sum_map]
  rw [← remaining, Finset.sum_map, area_eq] at bound
  change (∑ i ∈ Finset.univ \ delFin,
      angle (inverseStereographic (path i.val)) (inverseStereographic (path (i.val + 1)))) *
      d * Real.sin eta ≤ _ at bound
  simp only [framed_angle] at bound
  exact bound

/-- The half-angle bound for arbitrary positive minimum turn up to a straight angle. -/
theorem exists_omit_two_cyclic_spherical_chords {K : Set Plane}
    (compact : IsCompact K) (convex : Convex ℝ K) (disk : ∀ x ∈ K, ‖x‖ ≤ 1)
    {a b : Plane} (ha : a ∈ K) (hb : b ∈ K) {d : ℝ} (nonneg : 0 ≤ d)
    (diameter : d ≤ 2 * dist a b) (T : Plane ≃ₗᵢ[ℝ] Plane) (base : T a 1 = T b 1)
    {n : ℕ} (p : Fin (n + 1) → Plane) (points : ∀ i, p i ∈ K)
    (injective : Function.Injective p) {eta : ℝ} (eta_pos : 0 < eta) (eta_small : eta ≤ Real.pi)
    (minimum : ∀ i,
      eta ≤ angle (p (finRotate (n + 1) i) - p i)
        (p (finRotate (n + 1) (finRotate (n + 1) i)) - p (finRotate (n + 1) i)))
    (support : let q := Complex.orthonormalBasisOneI.repr.symm ∘ T ∘ p
      ∀ i j, 0 ≤ Complex.orientation.areaForm (q (finRotate (n + 1) i) - q i) (q j - q i))
    (positive : let q := Complex.orthonormalBasisOneI.repr.symm ∘ T ∘ p
      ∀ i, 0 < Complex.orientation.areaForm (q (finRotate (n + 1) i) - q i)
        (q (finRotate (n + 1) (finRotate (n + 1) i)) - q (finRotate (n + 1) i))) :
    ∃ omitted : Finset (Fin (n + 1)), omitted.card ≤ 2 ∧
      (∑ i ∈ Finset.univ \ omitted,
        angle (inverseStereographic (p i)) (inverseStereographic (p (finRotate (n + 1) i)))) *
        d * Real.sin (eta / 2) ≤ 16 * (volume : Measure Plane).real K :=
  exists_omit_two_cyclic_spherical_chords_of_small_minimum compact convex disk ha hb nonneg
    diameter T base p points injective (eta := eta / 2)
    (by linarith only [eta_pos]) (by linarith only [eta_small])
    (fun i => (by linarith only [eta_pos] : eta / 2 ≤ eta).trans (minimum i)) support positive

end Unfoldings.Cap
