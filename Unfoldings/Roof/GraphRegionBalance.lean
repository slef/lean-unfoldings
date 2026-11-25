module

public import Unfoldings.Roof.GraphRegionFaces

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
  have fix_bound (w : C.Vertex Set.univ) : |fix w| ≤ δ w := by
    unfold fix
    split_ifs <;> simp only [δ, abs_neg, abs_of_nonneg (K.interiorCurvature_nonneg w),
      abs_zero, le_refl, K.interiorCurvature_nonneg w]
  have fix_support (w : C.Vertex Set.univ) (off : V w ∉ curve) : fix w = 0 := by
    have absent : V w ∉ graphPoint f '' Set.Ioo a b :=
      fun h => off (Or.inl (Set.image_mono Set.Ioo_subset_Icc_self h))
    exact ite_eq_right absent
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
  have estimate := K.abs_graphLens_faceAngleDifference_add_correction_le_curvature hf hg
    c first last crossing sample sample_in sample_off curve fix fix_bound fix_support
    jordan (fun i => (included i).trans contained) aligned included avoids disjoint
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
  have normalized :
      |(∑ w, if V w ∈ curve then F w - G w else 0) + ∑ w, fix w| ≤
        C.totalInteriorAngularDefect Set.univ := by
    rwa [← compatible_deciders]
  exact (congrArg abs summed) ▸ normalized

end Unfoldings.ConvexRoof
