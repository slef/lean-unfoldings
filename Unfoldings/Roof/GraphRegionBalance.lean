module

public import Unfoldings.Roof.GraphRegionFaces
public import Unfoldings.Roof.GraphLensSignedCurvature

/-! Signed lens curvature controls the fixed-bank turn sum and the closing graph's fan sum. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

private theorem mem_graphPoint_image_iff {f : ℝ → ℝ} {I : Set ℝ} {p : Plane} :
    p ∈ graphPoint f '' I ↔ p 0 ∈ I ∧ p 1 = f (p 0) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, hh⟩
    refine ⟨p 0, hx, ?_⟩
    ext i
    fin_cases i
    · rfl
    · exact hh.symm

set_option maxHeartbeats 2300000 in
open Classical in
/-- The negative boundary balance is the curvature charge of the band between
the graphs. Each charge has the sign of the side of the closing graph. -/
theorem exists_signed_graph_boundaryAngleBalance {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ} {n : ℕ}
    (c : Fin (n + 2) ↪o ℝ) (first : c 0 = a) (last : c (Fin.last (n + 1)) = b)
    (crossing : Set.range c = {t ∈ Set.Icc a b | f t = g t})
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
    (aligned_f : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))
    (aligned_g : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint g '' Set.Icc a b))
    (flat_g : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b →
      C.interiorAngularDefect Set.univ w = 0)
    (right_bank : Bool) :
    let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
    let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
    let F := K.regionalAngleExcess (facesAboveGraph sample f a b)
    let G := K.regionalAngleExcess (facesAboveGraph sample g a b)
    let V (w : C.Vertex Set.univ) := K.projectedVertex w
    let δ := C.interiorAngularDefect Set.univ
    (curve ⊆ interior K.footprint) →
    (∀ i, Schoenflies.IsJordanCurve (J i)) →
    (∀ i, J i ⊆ curve) →
    (∀ i, Disjoint (interior (closedJordanDomain (J i))) curve) →
    (Pairwise fun i j => Disjoint (interior (closedJordanDomain (J i)))
      (interior (closedJordanDomain (J j)))) →
    ∃ weight : C.Vertex Set.univ → ℝ,
      (∀ w, |weight w| ≤ 1) ∧
      (∀ w, weight w ≠ 0 →
        V w 0 ∈ Set.Ioo a b ∧ V w 1 ∈ Set.uIcc (f (V w 0)) (g (V w 0)) ∧
          0 < (V w 1 - g (V w 0)) * weight w) ∧
      -( (∑ w, if V w ∈ graphPoint f '' Set.Ioo a b then F w + (if right_bank then δ w else 0) else 0) -
        (∑ w, if V w ∈ graphPoint g '' Set.Ioo a b then G w else 0) +
        (∑ w, if V w ∈ curve ∧ V w 0 ∉ Set.Ioo a b then F w - G w else 0)) =
          ∑ w, weight w * δ w := by
  dsimp only
  let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
  let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
  let F := K.regionalAngleExcess (facesAboveGraph sample f a b)
  let G := K.regionalAngleExcess (facesAboveGraph sample g a b)
  let V (w : C.Vertex Set.univ) := K.projectedVertex w
  let δ := C.interiorAngularDefect Set.univ
  intro contained jordan included avoids disjoint
  let fix (w : C.Vertex Set.univ) :=
    if V w ∈ graphPoint f '' Set.Ioo a b then
      if right_bank then (if V w 1 < g (V w 0) then δ w else 0)
      else (if g (V w 0) < V w 1 then -δ w else 0)
    else 0
  have sample_off (j : Face) (window : sample j 0 ∈ Set.Ioo a b) :
      sample j 1 ≠ f (sample j 0) ∧ sample j 1 ≠ g (sample j 0) :=
    ⟨fun equal => Set.disjoint_left.mp (aligned_f j) (sample_in j)
      (mem_graphPoint_image_iff.mpr ⟨Set.Ioo_subset_Icc_self window, equal⟩),
      fun equal => Set.disjoint_left.mp (aligned_g j) (sample_in j)
        (mem_graphPoint_image_iff.mpr ⟨Set.Ioo_subset_Icc_self window, equal⟩)⟩
  have aligned (i : Fin (n + 1)) (j : Face) :
      Disjoint (interior (K.projectedTriangle j).carrier) (J i) := by
    apply Disjoint.mono_right (included i)
    exact (aligned_f j).union_right (aligned_g j)
  have pointwise (w : C.Vertex Set.univ) :
      (if V w ∈ curve then F w - G w else 0) + fix w =
        (if V w ∈ graphPoint f '' Set.Ioo a b then F w + (if right_bank then δ w else 0) else 0) -
        (if V w ∈ graphPoint g '' Set.Ioo a b then G w else 0) +
        (if V w ∈ curve ∧ V w 0 ∉ Set.Ioo a b then F w - G w else 0) := by
    let p := V w
    let on_f := p ∈ graphPoint f '' Set.Ioo a b
    let on_g := p ∈ graphPoint g '' Set.Ioo a b
    change (if p ∈ curve then F w - G w else 0) + fix w =
      (if on_f then F w + (if right_bank then δ w else 0) else 0) -
      (if on_g then G w else 0) + (if p ∈ curve ∧ p 0 ∉ Set.Ioo a b then F w - G w else 0)
    by_cases window : p 0 ∈ Set.Ioo a b
    · have curve_iff : p ∈ curve ↔ on_f ∨ on_g := by
        simp only [curve, Set.mem_union, on_f, on_g, mem_graphPoint_image_iff, window,
          Set.Ioo_subset_Icc_self window, true_and]
      have interior_curve (h : on_f ∨ on_g) := contained (curve_iff.mpr h)
      simp only [window, not_true_eq_false, and_false, ite_false, add_zero]
      by_cases f_here : on_f
      · have at_f := (mem_graphPoint_image_iff.mp f_here).2
        rw [ite_eq_left (curve_iff.mpr (Or.inl f_here)), ite_eq_left f_here]
        have fix_value : fix w =
            (if right_bank then (if p 1 < g (p 0) then δ w else 0)
              else (if g (p 0) < p 1 then -δ w else 0)) :=
          ite_eq_left f_here
        rw [fix_value]
        by_cases g_here : on_g
        · have at_g := (mem_graphPoint_image_iff.mp g_here).2
          have zero : δ w = 0 := flat_g w g_here
          rw [ite_eq_left g_here, zero, neg_zero]
          cases right_bank <;> simp <;> ring
        · have off_g : p 1 ≠ g (p 0) := fun eq => g_here (mem_graphPoint_image_iff.mpr ⟨window, eq⟩)
          rw [ite_eq_right g_here, sub_zero]
          rcases lt_or_gt_of_ne off_g with below | above
          · have G_zero : G w = 0 := K.regionalAngleExcess_facesAboveGraph_of_below hg sample
              sample_in endpoints aligned_g below
            rw [G_zero, sub_zero, ite_eq_left below, ite_eq_right (not_lt_of_ge below.le)]
          · have G_value : G w = -δ w := K.regionalAngleExcess_facesAboveGraph_of_above hg sample
              sample_in endpoints aligned_g (interior_curve (Or.inl f_here)) window above
            rw [G_value, ite_eq_right (not_lt_of_ge above.le), ite_eq_left above]
            cases right_bank <;> simp <;> ring
      · have fixed : fix w = 0 := ite_eq_right f_here
        rw [fixed, add_zero, ite_eq_right f_here]
        by_cases g_here : on_g
        · rw [ite_eq_left (curve_iff.mpr (Or.inr g_here)), ite_eq_left g_here]
          have off_f : p 1 ≠ f (p 0) := fun eq => f_here (mem_graphPoint_image_iff.mpr ⟨window, eq⟩)
          have F_zero : F w = 0 := by
            rcases lt_or_gt_of_ne off_f with below | above
            · exact K.regionalAngleExcess_facesAboveGraph_of_below hf sample sample_in endpoints aligned_f below
            · exact (K.regionalAngleExcess_facesAboveGraph_of_above hf sample sample_in endpoints aligned_f
                (interior_curve (Or.inr g_here)) window above).trans (by rw [flat_g w g_here, neg_zero])
          rw [F_zero]
        · rw [ite_eq_right g_here, ite_eq_right (fun h => (curve_iff.mp h).elim f_here g_here), sub_zero]
    · have f_absent : ¬ on_f := fun h => window (mem_graphPoint_image_iff.mp h).1
      have g_absent : ¬ on_g := fun h => window (mem_graphPoint_image_iff.mp h).1
      have fixed : fix w = 0 := ite_eq_right f_absent
      simp only [window, not_false_eq_true, and_true, fixed, add_zero, ite_eq_right f_absent,
        ite_eq_right g_absent, sub_zero, zero_add]
  have summed := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun w _ => pointwise w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at summed
  have compatible_deciders :
      (∑ w, @ite ℝ (K.projectedVertex w ∈ curve) (Classical.propDecidable _)
        (F w - G w) 0) =
        ∑ w, if V w ∈ curve then F w - G w else 0 := by
    apply Finset.sum_congr rfl
    intro w _
    by_cases member : V w ∈ curve
    · exact (ite_eq_left member).trans (ite_eq_left member).symm
    · exact (ite_eq_right member).trans (ite_eq_right member).symm
  let interiorWeight (w : C.Vertex Set.univ) : ℝ :=
    ∑ i : Fin (n + 1), if V w ∈ interior (closedJordanDomain (J i)) then
      -graphLensSign f g (c i.castSucc) (c i.succ) else 0
  let bankWeight (w : C.Vertex Set.univ) : ℝ :=
    if V w ∈ graphPoint f '' Set.Ioo a b then
      if right_bank then (if V w 1 < g (V w 0) then -1 else 0)
      else (if g (V w 0) < V w 1 then 1 else 0)
    else 0
  let weight (w : C.Vertex Set.univ) := interiorWeight w + bankWeight w
  have zeros (w : C.Vertex Set.univ) (off : V w ∉ curve) : bankWeight w = 0 :=
    ite_eq_right (fun h => off (Or.inl (Set.image_mono Set.Ioo_subset_Icc_self h)))
  have bounds (w : C.Vertex Set.univ) : |bankWeight w| ≤ 1 := by
    unfold bankWeight
    split_ifs <;> norm_num
  have bank_sign (w : C.Vertex Set.univ) (nonzero : bankWeight w ≠ 0) :
      V w 0 ∈ Set.Ioo a b ∧ V w 1 ∈ Set.uIcc (f (V w 0)) (g (V w 0)) ∧
        0 < (V w 1 - g (V w 0)) * bankWeight w := by
    have member : V w ∈ graphPoint f '' Set.Ioo a b := by
      by_contra h
      exact nonzero (ite_eq_right h)
    obtain ⟨interval, he⟩ := mem_graphPoint_image_iff.mp member
    refine ⟨interval, he.symm ▸ Set.left_mem_uIcc, ?_⟩
    unfold bankWeight at nonzero ⊢
    rw [ite_eq_left member] at nonzero ⊢
    split_ifs at nonzero ⊢ <;> simp_all only [ne_eq, not_true_eq_false, mul_one] <;> linarith
  have projected (i : Fin (n + 1)) :
      c i.castSucc ∈ Set.Icc a b ∧ c i.succ ∈ Set.Icc a b ∧
      f (c i.castSucc) = g (c i.castSucc) ∧ f (c i.succ) = g (c i.succ) := by
    obtain ⟨range₀, eq₀⟩ := crossing.subset ⟨i.castSucc, rfl⟩
    obtain ⟨range₁, eq₁⟩ := crossing.subset ⟨i.succ, rfl⟩
    exact ⟨range₀, range₁, eq₀, eq₁⟩
  have lens_order (i : Fin (n + 1)) : c i.castSucc < c i.succ := c.strictMono (Fin.castSucc_lt_succ (i := i))
  have lens_sep (i : Fin (n + 1)) (t : ℝ) (mem : t ∈ Set.Ioo (c i.castSucc) (c i.succ)) :
      f t ≠ g t := by
    intro eq
    obtain ⟨j, rfl⟩ := crossing.symm.subset
      ⟨⟨(projected i).1.1.trans mem.1.le, mem.2.le.trans (projected i).2.1.2⟩, eq⟩
    have lo := c.strictMono.lt_iff_lt.mp mem.1
    have hi := c.strictMono.lt_iff_lt.mp mem.2
    have lp : i.val < j.val := lo
    have hp : j.val < i.val + 1 := hi
    omega
  have weight_data (w : C.Vertex Set.univ) : |weight w| ≤ 1 ∧
      (weight w ≠ 0 →
        V w 0 ∈ Set.Ioo a b ∧ V w 1 ∈ Set.uIcc (f (V w 0)) (g (V w 0)) ∧
          0 < (V w 1 - g (V w 0)) * weight w) := by
    by_cases enclosed : ∃ i, V w ∈ interior (closedJordanDomain (J i))
    · obtain ⟨i, mem⟩ := enclosed
      have eq : interiorWeight w = -graphLensSign f g (c i.castSucc) (c i.succ) := by
        unfold interiorWeight
        rw [Finset.sum_eq_single i, ite_eq_left mem]
        · intro j _ diff
          exact ite_eq_right (fun hit => Set.disjoint_left.mp (disjoint diff) hit mem)
        · simp
      have off : V w ∉ curve := fun h => Set.disjoint_left.mp (avoids i) mem h
      have signed : weight w = -graphLensSign f g (c i.castSucc) (c i.succ) := by
        simp only [weight, eq, zeros w off, add_zero]
      rw [signed]
      constructor
      · unfold graphLensSign
        split_ifs <;> norm_num
      · intro _
        obtain ⟨left_win, right_win, l_eq, r_eq⟩ := projected i
        have geometry := mem
        change V w ∈ interior (closedJordanDomain (graphLens f g (c i.castSucc) (c i.succ))) at geometry
        rw [interior_closedJordanDomain_graphLens hf hg (lens_order i) l_eq r_eq (lens_sep i)] at geometry
        exact ⟨⟨left_win.1.trans_lt geometry.1.1, geometry.1.2.trans_le right_win.2⟩,
          ⟨geometry.2.1.le, geometry.2.2.le⟩,
          graphLens_negSign_mul_height_pos hf hg (lens_order i) l_eq r_eq (lens_sep i) mem⟩
    · have eq : interiorWeight w = 0 := Finset.sum_eq_zero (fun i _ =>
        ite_eq_right (fun h => enclosed ⟨i, h⟩))
      simpa only [weight, eq, zero_add] using ⟨bounds w, bank_sign w⟩
  have exact_lenses := K.graphLens_boundarySum_eq_signed_defects hf hg c first last crossing
    sample sample_in sample_off curve jordan (fun i => (included i).trans contained)
    aligned included avoids
  have exact_bulk : -(∑ w, if V w ∈ curve then F w - G w else 0) =
      ∑ w, interiorWeight w * δ w := by
    rw [← compatible_deciders, exact_lenses, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro w _
    unfold interiorWeight
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : V w ∈ interior (closedJordanDomain (J i))
    · rw [ite_eq_left h, ite_eq_left h, neg_mul]
    · rw [ite_eq_right h, ite_eq_right h, neg_zero, zero_mul]
  have exact_bank (w : C.Vertex Set.univ) : -fix w = bankWeight w * δ w := by
    unfold fix bankWeight
    split_ifs <;> ring
  refine ⟨weight, fun w => (weight_data w).1, fun w => (weight_data w).2, ?_⟩
  rw [← summed, neg_add, exact_bulk, ← Finset.sum_neg_distrib]
  simp_rw [exact_bank]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  exact (add_mul _ _ _).symm

set_option maxHeartbeats 2300000 in
open Classical in
/-- Compare the actual regional angles along the two graphs. Taking the
lower bank adds its complementary defect, in the same curvature budget. -/
theorem abs_graph_boundaryAngleBalance_le {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a b : ℝ} {n : ℕ}
    (c : Fin (n + 2) ↪o ℝ) (first : c 0 = a) (last : c (Fin.last (n + 1)) = b)
    (crossing : Set.range c = {t ∈ Set.Icc a b | f t = g t})
    (sample : Face → Plane) (sample_in : ∀ j, sample j ∈ interior (K.projectedTriangle j).carrier)
    (endpoints : ∀ i z, z ∈ interior (K.projectedTriangle i).carrier → z 0 ≠ a ∧ z 0 ≠ b)
    (aligned_f : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))
    (aligned_g : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint g '' Set.Icc a b))
    (flat_g : ∀ w : C.Vertex Set.univ, K.projectedVertex w ∈ graphPoint g '' Set.Ioo a b →
      C.interiorAngularDefect Set.univ w = 0)
    (right_bank : Bool) :
    let curve := (graphPoint f '' Set.Icc a b) ∪ (graphPoint g '' Set.Icc a b)
    let J (i : Fin (n + 1)) := graphLens f g (c i.castSucc) (c i.succ)
    let F := K.regionalAngleExcess (facesAboveGraph sample f a b)
    let G := K.regionalAngleExcess (facesAboveGraph sample g a b)
    let V (w : C.Vertex Set.univ) := K.projectedVertex w
    let δ := C.interiorAngularDefect Set.univ
    (curve ⊆ interior K.footprint) →
    (∀ i, Schoenflies.IsJordanCurve (J i)) →
    (∀ i, J i ⊆ curve) →
    (∀ i, Disjoint (interior (closedJordanDomain (J i))) curve) →
    (Pairwise fun i j => Disjoint (interior (closedJordanDomain (J i)))
      (interior (closedJordanDomain (J j)))) →
    |(∑ w, if V w ∈ graphPoint f '' Set.Ioo a b then F w + (if right_bank then δ w else 0) else 0) -
      (∑ w, if V w ∈ graphPoint g '' Set.Ioo a b then G w else 0) +
      (∑ w, if V w ∈ curve ∧ V w 0 ∉ Set.Ioo a b then F w - G w else 0)| ≤
        C.totalInteriorAngularDefect Set.univ := by
  dsimp only
  intro contained jordan included avoids disjoint
  obtain ⟨weight, bounded, _, exact_signed⟩ :=
    K.exists_signed_graph_boundaryAngleBalance hf hg c first last crossing sample sample_in
      endpoints aligned_f aligned_g flat_g right_bank contained jordan included avoids disjoint
  rw [← abs_neg, exact_signed]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun w _ => ?_))
  rw [abs_mul, abs_of_nonneg (K.interiorCurvature_nonneg w)]
  exact mul_le_of_le_one_left (K.interiorCurvature_nonneg w) (bounded w)

end Unfoldings.ConvexRoof
