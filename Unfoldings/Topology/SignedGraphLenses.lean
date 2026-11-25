module

public import Unfoldings.Topology.GraphLensInterior

/-! Signed lens indicators compute the difference of the two upper graph regions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- Every time strictly between the endpoints and away from the listed
crossings lies in exactly one successive open interval. -/
theorem exists_unique_openCrossingInterval {n : ℕ} (c : Fin (n + 2) ↪o ℝ)
    {t : ℝ} (after : c 0 < t) (before : t < c (Fin.last (n + 1)))
    (absent : t ∉ Set.range c) :
    ∃! i : Fin (n + 1), t ∈ Set.Ioo (c i.castSucc) (c i.succ) := by
  classical
  let later := Finset.univ.filter (fun j : Fin (n + 2) => t < c j)
  have nonempty : later.Nonempty := ⟨Fin.last (n + 1), by simpa [later] using before⟩
  let j := later.min' nonempty
  have j_mem : j ∈ later := later.min'_mem nonempty
  have upper : t < c j := (Finset.mem_filter.mp j_mem).2
  have positive : 0 < j.val := by
    by_contra! h
    have zero : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero h)
    exact after.not_ge (zero ▸ upper.le)
  let i : Fin (n + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
  have next : i.succ = j := Fin.ext (by change j.val - 1 + 1 = j.val; omega)
  have before_j : i.castSucc < j := next ▸ Fin.castSucc_lt_succ
  have first : c i.castSucc < t := by
    by_contra! not_before
    have distinct : t ≠ c i.castSucc := fun h => absent ⟨i.castSucc, h.symm⟩
    have included : i.castSucc ∈ later :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne not_before distinct⟩
    exact before_j.not_ge (later.min'_le _ included)
  have last : t < c i.succ := next.symm ▸ upper
  refine ⟨i, ⟨first, last⟩, fun k hk => ?_⟩
  rcases lt_trichotomy k i with smaller | same | larger
  · exact (first.not_ge ((c.monotone (show k.succ ≤ i.castSucc from smaller)).trans' hk.2.le)).elim
  · exact same
  · exact (last.not_ge ((c.monotone (show i.succ ≤ k.castSucc from larger)).trans hk.1.le)).elim

/-- The graphs do not switch vertical order within the interior of a lens. -/
theorem graph_order_iff_at {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (separate : ∀ u ∈ Set.Ioo a b, f u ≠ g u) :
    f s < g s ↔ f t < g t := by
  have interval : IsPreconnected (Set.Ioo a b) := isPreconnected_Ioo
  have image := interval.image (fun u => g u - f u) (hg.sub hf).continuousOn
  have absent : (0 : ℝ) ∉ (fun u => g u - f u) '' Set.Ioo a b := by
    rintro ⟨u, hu, equal⟩
    exact separate u hu (sub_eq_zero.mp equal).symm
  have positive {u v : ℝ} (hu : u ∈ Set.Ioo a b) (hv : v ∈ Set.Ioo a b)
      (bound : f u < g u) : f v < g v := by
    by_contra! failure
    exact absent (image.Icc_subset (Set.mem_image_of_mem _ hv) (Set.mem_image_of_mem _ hu)
      ⟨sub_nonpos.mpr failure, sub_nonneg.mpr bound.le⟩)
  exact ⟨positive hs ht, positive ht hs⟩

/-- The indicator of the part of the vertical slab strictly above a graph. -/
def upperGraphWeight (f : ℝ → ℝ) (a b : ℝ) (p : Plane) : ℝ :=
  if p 0 ∈ Set.Ioo a b ∧ f (p 0) < p 1 then 1 else 0

/-- The sign of the lens as the bank is traversed in increasing horizontal order. -/
def graphLensSign (f g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if f ((a + b) / 2) < g ((a + b) / 2) then 1 else -1

private theorem above_sub_of_lt {l h y : ℝ} (ordered : l < h) (off_upper : y ≠ h) :
    ((if l < y then 1 else 0) - (if h < y then 1 else 0) : ℝ) =
      if l < y ∧ y < h then 1 else 0 := by
  by_cases first : l < y
  · rcases lt_or_gt_of_ne off_upper with below | above
    · simp [first, below, below.not_gt]
    · simp [first, above, above.not_gt]
  · have last : ¬ h < y := fun after => first (ordered.trans after)
    simp [first, last]

open Classical in
/-- The difference of the two upper-face indicators equals the signed sum of
the lens indicators at any point off the curves. -/
theorem upperGraphWeight_sub_eq_sum_lenses {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ} {n : ℕ}
    (c : Fin (n + 2) ↪o ℝ) (first : c 0 = a) (last : c (Fin.last (n + 1)) = b)
    (crossing : Set.range c = {t ∈ Set.Icc a b | f t = g t}) (p : Plane)
    (regular : p 0 ∈ Set.Ioo a b → p 1 ≠ f (p 0) ∧ p 1 ≠ g (p 0)) :
    upperGraphWeight f a b p - upperGraphWeight g a b p =
      ∑ i : Fin (n + 1), graphLensSign f g (c i.castSucc) (c i.succ) *
        (if p ∈ interior (closedJordanDomain (graphLens f g (c i.castSucc) (c i.succ)))
          then 1 else 0) := by
  let t := p 0
  let between (i : Fin (n + 1)) := Set.Ioo (c i.castSucc) (c i.succ)
  have at_cross (j : Fin (n + 2)) : f (c j) = g (c j) :=
    (crossing.subset (Set.mem_range_self j)).2
  have ordered (i : Fin (n + 1)) : c i.castSucc < c i.succ :=
    c.strictMono (Fin.castSucc_lt_succ (i := i))
  have mid (i : Fin (n + 1)) : (c i.castSucc + c i.succ) / 2 ∈ between i := by
    exact ⟨by linarith only [ordered i], by linarith only [ordered i]⟩
  have slab (i : Fin (n + 1)) : between i ⊆ Set.Ioo a b := by
    intro s hs
    have left := c.monotone (Fin.zero_le i.castSucc)
    have right := c.monotone (Fin.le_last i.succ)
    exact ⟨(first ▸ left).trans_lt hs.1, hs.2.trans_le (last ▸ right)⟩
  have away (i : Fin (n + 1)) {s : ℝ} (hs : s ∈ between i) : s ∉ Set.range c := by
    rintro ⟨j, rfl⟩
    have lo : i.val < j.val := c.lt_iff_lt.mp hs.1
    have hi : j.val < i.val + 1 := c.lt_iff_lt.mp hs.2
    omega
  have separate (i : Fin (n + 1)) (s : ℝ) (hs : s ∈ between i) : f s ≠ g s := by
    intro same
    exact away i hs (crossing.symm.subset ⟨Set.Ioo_subset_Icc_self (slab i hs), same⟩)
  have inside (i : Fin (n + 1)) :
      p ∈ interior (closedJordanDomain (graphLens f g (c i.castSucc) (c i.succ))) ↔
        t ∈ between i ∧ min (f t) (g t) < p 1 ∧ p 1 < max (f t) (g t) := by
    rw [interior_closedJordanDomain_graphLens hf hg (ordered i) (at_cross _) (at_cross _) (separate i)]
    rfl
  by_cases active : t ∈ Set.Ioo a b ∧ f t ≠ g t
  · have no_crossing : t ∉ Set.range c := fun h => active.2 (crossing.subset h).2
    obtain ⟨i, in_i, unique⟩ := exists_unique_openCrossingInterval c
      (first.symm ▸ active.1.1) (last.symm ▸ active.1.2) no_crossing
    have at_i := (graph_order_iff_at hf hg (mid i) in_i (separate i))
    have total :
        (∑ j : Fin (n + 1), graphLensSign f g (c j.castSucc) (c j.succ) *
          (if p ∈ interior (closedJordanDomain (graphLens f g (c j.castSucc) (c j.succ)))
            then 1 else 0)) =
          graphLensSign f g (c i.castSucc) (c i.succ) *
            (if p ∈ interior (closedJordanDomain (graphLens f g (c i.castSucc) (c i.succ)))
              then 1 else 0) := by
      apply Finset.sum_eq_single i
      · intro j _ different
        rw [inside j, ite_eq_right (fun h => different (unique j h.1)), mul_zero]
      · simp
    rw [total, inside i]
    have active_time : p 0 ∈ Set.Ioo a b := active.1
    have lens_time : p 0 ∈ Set.Ioo (c i.castSucc) (c i.succ) := in_i
    simp only [upperGraphWeight, t, between, active_time, lens_time, true_and]
    unfold graphLensSign
    have neq := regular active.1
    rcases lt_or_gt_of_ne active.2 with before | after
    · rw [ite_eq_left (at_i.mpr before), min_eq_left before.le, max_eq_right before.le, one_mul]
      exact above_sub_of_lt before neq.2
    · rw [ite_eq_right (fun h => (at_i.mp h).not_ge after.le),
        min_eq_right after.le, max_eq_left after.le, neg_one_mul, ← neg_sub]
      exact congrArg Neg.neg (above_sub_of_lt after neq.1)
  · have no_lens (i : Fin (n + 1)) :
        p ∉ interior (closedJordanDomain (graphLens f g (c i.castSucc) (c i.succ))) := by
      intro h
      have ht := ((inside i).mp h).1
      exact active ⟨slab i ht, separate i t ht⟩
    simp only [no_lens, ite_false, mul_zero, Finset.sum_const_zero]
    by_cases time : t ∈ Set.Ioo a b
    · have equal : f t = g t := Classical.not_not.mp (fun ne => active ⟨time, ne⟩)
      unfold upperGraphWeight
      change ((if t ∈ Set.Ioo a b ∧ f t < p 1 then 1 else 0) -
        (if t ∈ Set.Ioo a b ∧ g t < p 1 then 1 else 0) : ℝ) = 0
      rw [equal, sub_self]
    · simp [upperGraphWeight, show p 0 ∉ Set.Ioo a b from time]

end Unfoldings.PlanarTopology
