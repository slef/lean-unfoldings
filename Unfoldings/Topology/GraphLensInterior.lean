module

public import Unfoldings.Topology.OrderedGraphLenses

/-! The bounded component between two ordered graph arcs is the open strip between them. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PlanarTopology

/-- The interior of a graph lens has the exact pointwise vertical bounds.
This determines which one-sided bank fan faces the disk. -/
theorem interior_closedJordanDomain_graphLens {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ}
    (ordered : a < b) (start : f a = g a) (finish : f b = g b)
    (separate : ∀ t ∈ Set.Ioo a b, f t ≠ g t) :
    interior (closedJordanDomain (graphLens f g a b)) =
      {p : Plane | p 0 ∈ Set.Ioo a b ∧ min (f (p 0)) (g (p 0)) < p 1 ∧
        p 1 < max (f (p 0)) (g (p 0))} := by
  let J := graphLens f g a b
  let lo (t : ℝ) := min (f t) (g t)
  let hi (t : ℝ) := max (f t) (g t)
  let U := {p : Plane | p 0 ∈ Set.Ioo a b ∧ lo (p 0) < p 1 ∧ p 1 < hi (p 0)}
  have jordan : Schoenflies.IsJordanCurve J :=
    isJordanCurve_two_graphs f g hf hg ordered start finish separate
  let region := Schoenflies.jordan_curve_theorem jordan
  have shallow : interior (closedJordanDomain J) = Schoenflies.inside J := by
    apply Set.Subset.antisymm _ (region.isOpen_inside.subset_interior_iff.mpr subset_closure)
    intro p hp
    by_contra absent
    have border : p ∈ frontier (Schoenflies.inside J) := by
      rw [frontier, region.isOpen_inside.interior_eq]
      exact ⟨interior_subset hp, absent⟩
    have edge : p ∈ frontier (closedJordanDomain J) :=
      (frontier_closedJordanDomain jordan).symm.subset (region.frontier_inside.subset border)
    exact edge.2 hp
  have inside_subset : Schoenflies.inside J ⊆ U := by
    intro p hp
    have h_x := interior_two_graphs_subset_open_slab jordan (shallow.symm.subset hp)
    have avoids : p ∉ J := Schoenflies.inside_subset_compl hp
    have unequal_f : p 1 ≠ f (p 0) := by
      intro at_f
      apply avoids
      refine Or.inl ⟨p 0, Set.Ioo_subset_Icc_self h_x, ?_⟩
      apply PiLp.ext
      intro j
      fin_cases j
      · rfl
      · exact at_f.symm
    have unequal_g : p 1 ≠ g (p 0) := by
      intro at_g
      apply avoids
      refine Or.inr ⟨p 0, Set.Ioo_subset_Icc_self h_x, ?_⟩
      apply PiLp.ext
      intro j
      fin_cases j
      · rfl
      · exact at_g.symm
    let u : Plane := WithLp.toLp 2 ![0, 1]
    have u_ne : u ≠ 0 := by
      intro h
      have eq := congrArg (fun z : Plane => z 1) h
      norm_num [u] at eq
    have no_escape (d : Plane) (nonzero : d ≠ 0)
        (miss : ∀ r : ℝ, 0 ≤ r → p + r • d ∉ J) : False :=
      not_isBounded_component_of_escape_ray nonzero miss
        ((region.connectedComponentIn_eq_inside hp).symm ▸ region.isBounded_inside)
    refine ⟨h_x, ?_, ?_⟩
    · by_contra! outside
      have low_f : p 1 < f (p 0) :=
        lt_of_le_of_ne (outside.trans (min_le_left _ _)) unequal_f
      have low_g : p 1 < g (p 0) :=
        lt_of_le_of_ne (outside.trans (min_le_right _ _)) unequal_g
      apply no_escape (-u) (neg_ne_zero.mpr u_ne)
      rintro r nonneg (⟨t, _, at_f⟩ | ⟨t, _, at_g⟩)
      · have time : t = p 0 := by
          simpa [graphPoint, u, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply] using
            congrArg (fun z : Plane => z 0) at_f
        have height : f (p 0) = p 1 - r := by
          simpa [graphPoint, time, u, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, sub_eq_add_neg] using
            congrArg (fun z : Plane => z 1) at_f
        linarith only [height, nonneg, low_f]
      · have time : t = p 0 := by
          simpa [graphPoint, u, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply] using
            congrArg (fun z : Plane => z 0) at_g
        have height : g (p 0) = p 1 - r := by
          simpa [graphPoint, time, u, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, sub_eq_add_neg] using
            congrArg (fun z : Plane => z 1) at_g
        linarith only [height, nonneg, low_g]
    · by_contra! outside
      have high_f : f (p 0) < p 1 :=
        lt_of_le_of_ne ((le_max_left _ _).trans outside) unequal_f.symm
      have high_g : g (p 0) < p 1 :=
        lt_of_le_of_ne ((le_max_right _ _).trans outside) unequal_g.symm
      apply no_escape u u_ne
      rintro r nonneg (⟨t, _, at_f⟩ | ⟨t, _, at_g⟩)
      · have time : t = p 0 := by
          simpa [graphPoint, u, PiLp.add_apply, PiLp.smul_apply] using congrArg (fun z : Plane => z 0) at_f
        have height : f (p 0) = p 1 + r := by
          simpa [graphPoint, time, u, PiLp.add_apply, PiLp.smul_apply] using
            congrArg (fun z : Plane => z 1) at_f
        linarith only [height, nonneg, high_f]
      · have time : t = p 0 := by
          simpa [graphPoint, u, PiLp.add_apply, PiLp.smul_apply] using congrArg (fun z : Plane => z 0) at_g
        have height : g (p 0) = p 1 + r := by
          simpa [graphPoint, time, u, PiLp.add_apply, PiLp.smul_apply] using
            congrArg (fun z : Plane => z 1) at_g
        linarith only [height, nonneg, high_g]
  have width (t : ℝ) (ht : t ∈ Set.Ioo a b) : lo t < hi t := by
    rcases lt_or_gt_of_ne (separate t ht) with lower | upper
    · simp only [lo, hi, min_eq_left lower.le, max_eq_right lower.le]
      exact lower
    · simp only [lo, hi, min_eq_right upper.le, max_eq_left upper.le]
      exact upper
  let box := Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) 1
  let move (s : ℝ × ℝ) : Plane :=
    WithLp.toLp 2 ![s.1, lo s.1 + s.2 * (hi s.1 - lo s.1)]
  have continuous_move : Continuous move := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_fst
    · have lo_cont := hf.min hg
      have hi_cont := hf.max hg
      exact (lo_cont.comp continuous_fst).add
        (continuous_snd.mul ((hi_cont.comp continuous_fst).sub (lo_cont.comp continuous_fst)))
  have image : move '' box = U := by
    ext p
    constructor
    · rintro ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
      change t ∈ Set.Ioo a b ∧ lo t < lo t + s * (hi t - lo t) ∧
        lo t + s * (hi t - lo t) < hi t
      have positive := sub_pos.mpr (width t ht)
      exact ⟨ht, by linarith only [mul_pos hs.1 positive],
        by linarith only [mul_lt_mul_of_pos_right hs.2 positive]⟩
    · rintro ⟨ht, above, below⟩
      let t := p 0
      let s := (p 1 - lo t) / (hi t - lo t)
      have positive : 0 < hi t - lo t := sub_pos.mpr (width t ht)
      refine ⟨(t, s), ⟨ht, div_pos (sub_pos.mpr above) positive,
        (div_lt_one positive).mpr (sub_lt_sub_right below _)⟩, ?_⟩
      apply PiLp.ext
      intro j
      fin_cases j
      · rfl
      · change lo t + s * (hi t - lo t) = p 1
        rw [show s * (hi t - lo t) = p 1 - lo t from div_mul_cancel₀ _ positive.ne']
        ring
  have connected : IsPreconnected U := image ▸
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ continuous_move.continuousOn
  have misses : U ⊆ Jᶜ := by
    intro p hp
    rintro (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩)
    · have y : min (f t) (g t) < f t ∧ f t < max (f t) (g t) := hp.2
      rcases le_total (f t) (g t) with below | above
      · exact y.1.not_ge (min_eq_left below).ge
      · exact y.2.not_ge (max_eq_left above).le
    · have y : min (f t) (g t) < g t ∧ g t < max (f t) (g t) := hp.2
      rcases le_total (g t) (f t) with below | above
      · exact y.1.not_ge (min_eq_right below).ge
      · exact y.2.not_ge (max_eq_right above).le
  obtain ⟨p, hp⟩ := region.isConnected_inside.nonempty
  have subsets := connected.subset_connectedComponentIn (inside_subset hp) misses
  rw [region.connectedComponentIn_eq_inside hp] at subsets
  exact shallow.trans (Set.Subset.antisymm inside_subset subsets)

end Unfoldings.PlanarTopology
