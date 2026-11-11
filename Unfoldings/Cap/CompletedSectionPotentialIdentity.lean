module

public import Unfoldings.Cap.CompletedSectionCounterGeometry
public import Unfoldings.Cap.CompletedTracePhaseTransport

/-! Constructed completed-bank phases equal differences of the bounded crossing potential. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} (R : K.RadialCutForest source cuts)

/-- Repeated actual face labels contribute zero actual potential change. -/
theorem sectionPotential_change_same_face {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (same : T.face i.castSucc = T.face i.succ) :
    R.sectionCurvaturePotential p q (T.middleTime i.succ) -
      R.sectionCurvaturePotential p q (T.middleTime i.castSucc) = 0 := by
  classical
  rw [R.sectionCurvaturePotential_sub]
  apply Finset.sum_eq_zero
  intro v _
  by_cases nonroot : v ∉ R.spanningCompletion.parents.roots
  · rw [ite_eq_left nonroot,
      R.parent_counter_change_zero_of_same_face T different regular i same ⟨v, nonroot⟩, zero_mul]
  · exact ite_eq_right nonroot

/-- The actual original transition seam contributes exactly its geometric signed phase. -/
theorem sectionPotential_change_seam {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (s : C.Seam)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge) :
    R.sectionCurvaturePotential p q (T.middleTime i.succ) -
      R.sectionCurvaturePotential p q (T.middleTime i.castSucc) = R.seamSectionPhase s (q - p) := by
  classical
  rw [R.sectionCurvaturePotential_sub]
  by_cases kept : s ∈ R.completedRetain
  · simp only [seamSectionPhase, dite_eq_left kept]
    apply Finset.sum_eq_zero
    intro v _
    by_cases nonroot : v ∉ R.spanningCompletion.parents.roots
    · rw [ite_eq_left nonroot]
      have counter : R.parentSectionCounter p q (T.middleTime i.succ) v -
          R.parentSectionCounter p q (T.middleTime i.castSucc) v = 0 := by
        by_contra changes
        have named := R.parent_counter_change_eq_transition T different regular i s crossing
          ⟨v, nonroot⟩ changes
        exact kept ⟨⟨v, nonroot⟩, named⟩
      rw [counter, zero_mul]
    · exact ite_eq_right nonroot
  · let e := R.cutParent s kept
    have named : R.spanningCompletion.selection.edge e = s := R.cutParent_edge s kept
    simp only [seamSectionPhase, dite_eq_right kept]
    rw [Finset.sum_eq_single e.val]
    · rw [ite_eq_left e.property]
      apply R.parent_counter_change_mul_curvature T different regular i e
      simpa only [named] using crossing
    · intro v _ unequal
      by_cases nonroot : v ∉ R.spanningCompletion.parents.roots
      · rw [ite_eq_left nonroot]
        have counter : R.parentSectionCounter p q (T.middleTime i.succ) v -
            R.parentSectionCounter p q (T.middleTime i.castSucc) v = 0 := by
          by_contra changes
          have same_seam := R.parent_counter_change_eq_transition T different regular i s crossing
            ⟨v, nonroot⟩ changes
          have same_parent := R.spanningCompletion.selection.edge_injective (same_seam.trans
            named.symm)
          exact unequal (congrArg Subtype.val same_parent)
        rw [counter, zero_mul]
      · exact ite_eq_right nonroot
    · intro missing
      exact (missing (Finset.mem_univ _)).elim

/-- Every constructed actual phase is the corresponding actual potential difference. -/
theorem actualSectionPhase_eq_potential_change {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) {phase : ℝ} (actual : R.ActualSectionPhase T i phase) :
    phase = R.sectionCurvaturePotential p q (T.middleTime i.succ) -
      R.sectionCurvaturePotential p q (T.middleTime i.castSucc) := by
  cases actual with
  | same same => exact (R.sectionPotential_change_same_face T different regular i same).symm
  | seam s _faces crossing _transverse =>
    exact (R.sectionPotential_change_seam T different regular i s crossing).symm

/-- The whole signed sum is bounded by twice total cap curvature, independently of mesh size. -/
theorem abs_sum_actualSectionPhases_le (wedges : R.CurvedPathWedges)
    {p q : Plane} (T : K.SectionFaceTrace p q) (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (phase : Fin T.turns → ℝ) (actual : ∀ i, R.ActualSectionPhase T i (phase i)) :
    |∑ i, phase i| ≤ 2 * C.totalInteriorAngularDefect Set.univ := by
  have phases : (∑ i, phase i) =
      R.sectionCurvaturePotential p q (T.middleTime (Fin.last T.turns)) -
        R.sectionCurvaturePotential p q (T.middleTime 0) := by
    calc
      _ = ∑ i : Fin T.turns, (R.sectionCurvaturePotential p q (T.middleTime i.succ) -
          R.sectionCurvaturePotential p q (T.middleTime i.castSucc)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact R.actualSectionPhase_eq_potential_change T different regular i (actual i)
      _ = _ := sum_fin_succ_sub (fun i => R.sectionCurvaturePotential p q (T.middleTime i))
  rw [phases]
  calc
    _ ≤ |R.sectionCurvaturePotential p q (T.middleTime (Fin.last T.turns))| +
        |R.sectionCurvaturePotential p q (T.middleTime 0)| := abs_sub _ _
    _ ≤ C.totalInteriorAngularDefect Set.univ + C.totalInteriorAngularDefect Set.univ :=
      add_le_add (R.abs_sectionCurvaturePotential_le wedges p q _)
        (R.abs_sectionCurvaturePotential_le wedges p q _)
    _ = _ := by ring

end Unfoldings.ConvexCap.RadialCutForest
