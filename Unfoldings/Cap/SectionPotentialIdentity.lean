module

public import Unfoldings.Cap.SectionCounterGeometry
public import Unfoldings.Cap.TracePhaseTransport

/-!
# Actual trace phases are differences of the bounded crossing potential

All other original parent counters stay constant between adjacent interior
samples. The unique selected transition contributes exactly its actual signed
bank phase; retained transitions and repeated labels contribute zero. The whole
actual phase sum therefore telescopes before any absolute-value estimate.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

/-- Repeated actual face labels contribute zero actual potential change. -/
theorem sectionPotential_change_same_face {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (same : T.face i.castSucc = T.face i.succ) :
    M.sectionCurvaturePotential p q (T.middleTime i.succ) -
      M.sectionCurvaturePotential p q (T.middleTime i.castSucc) = 0 := by
  classical
  rw [M.sectionCurvaturePotential_sub]
  apply Finset.sum_eq_zero
  intro v _
  by_cases nonroot : v ∉ M.parents.roots
  · rw [ite_eq_left nonroot,
      M.parent_counter_change_zero_of_same_face T different regular i same ⟨v, nonroot⟩, zero_mul]
  · exact ite_eq_right nonroot

/-- The actual original transition seam contributes exactly its geometric signed phase. -/
theorem sectionPotential_change_seam {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) (s : C.Seam)
    (crossing : T.point i.castSucc.succ ∈
      (K.projectedTriangle (C.left s).face).edge (C.left s).edge) :
    M.sectionCurvaturePotential p q (T.middleTime i.succ) -
      M.sectionCurvaturePotential p q (T.middleTime i.castSucc) = M.seamSectionPhase s (q - p) := by
  classical
  rw [M.sectionCurvaturePotential_sub]
  by_cases kept : s ∈ M.retain
  · simp only [seamSectionPhase, dite_eq_left kept]
    apply Finset.sum_eq_zero
    intro v _
    by_cases nonroot : v ∉ M.parents.roots
    · rw [ite_eq_left nonroot]
      have counter : M.parentSectionCounter p q (T.middleTime i.succ) v -
          M.parentSectionCounter p q (T.middleTime i.castSucc) v = 0 := by
        by_contra changes
        have named := M.parent_counter_change_eq_transition T different regular i s crossing
          ⟨v, nonroot⟩ changes
        exact kept ⟨⟨v, nonroot⟩, named⟩
      rw [counter, zero_mul]
    · exact ite_eq_right nonroot
  · let e := M.cutParent s kept
    have named : M.selection.edge e = s := M.cutParent_edge s kept
    simp only [seamSectionPhase, dite_eq_right kept]
    rw [Finset.sum_eq_single e.val]
    · rw [ite_eq_left e.property]
      apply M.parent_counter_change_mul_curvature T different regular i e
      simpa only [named] using crossing
    · intro v _ unequal
      by_cases nonroot : v ∉ M.parents.roots
      · rw [ite_eq_left nonroot]
        have counter : M.parentSectionCounter p q (T.middleTime i.succ) v -
            M.parentSectionCounter p q (T.middleTime i.castSucc) v = 0 := by
          by_contra changes
          have same_seam := M.parent_counter_change_eq_transition T different regular i s crossing
            ⟨v, nonroot⟩ changes
          have same_parent := M.selection.edge_injective (same_seam.trans named.symm)
          exact unequal (congrArg Subtype.val same_parent)
        rw [counter, zero_mul]
      · exact ite_eq_right nonroot
    · intro missing
      exact (missing (Finset.mem_univ _)).elim

/-- Every constructed actual phase is the corresponding actual potential difference. -/
theorem actualSectionPhase_eq_potential_change {p q : Plane} (T : K.SectionFaceTrace p q)
    (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (i : Fin T.turns) {phase : ℝ} (actual : M.ActualSectionPhase T i phase) :
    phase = M.sectionCurvaturePotential p q (T.middleTime i.succ) -
      M.sectionCurvaturePotential p q (T.middleTime i.castSucc) := by
  cases actual with
  | same same => exact (M.sectionPotential_change_same_face T different regular i same).symm
  | seam s _faces crossing _transverse =>
    exact (M.sectionPotential_change_seam T different regular i s crossing).symm

/-- The whole signed sum is bounded by twice total cap curvature, independently of mesh size. -/
theorem abs_sum_actualSectionPhases_le (positive : 0 < t) (small : t < 1)
    {p q : Plane} (T : K.SectionFaceTrace p q) (different : p ≠ q)
    (regular : ∀ t : ℝ, ∀ f j, AffineMap.lineMap p q t ≠ (K.projectedTriangle f).vertex j)
    (phase : Fin T.turns → ℝ) (actual : ∀ i, M.ActualSectionPhase T i (phase i)) :
    |∑ i, phase i| ≤ 2 * C.totalInteriorAngularDefect Set.univ := by
  have phases : (∑ i, phase i) =
      M.sectionCurvaturePotential p q (T.middleTime (Fin.last T.turns)) -
        M.sectionCurvaturePotential p q (T.middleTime 0) := by
    calc
      _ = ∑ i : Fin T.turns, (M.sectionCurvaturePotential p q (T.middleTime i.succ) -
          M.sectionCurvaturePotential p q (T.middleTime i.castSucc)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact M.actualSectionPhase_eq_potential_change T different regular i (actual i)
      _ = _ := sum_fin_succ_sub (fun i => M.sectionCurvaturePotential p q (T.middleTime i))
  rw [phases]
  calc
    _ ≤ |M.sectionCurvaturePotential p q (T.middleTime (Fin.last T.turns))| +
        |M.sectionCurvaturePotential p q (T.middleTime 0)| := abs_sub _ _
    _ ≤ C.totalInteriorAngularDefect Set.univ + C.totalInteriorAngularDefect Set.univ :=
      add_le_add (M.abs_sectionCurvaturePotential_le positive small p q _)
        (M.abs_sectionCurvaturePotential_le positive small p q _)
    _ = _ := by ring

end Unfoldings.ConvexCap.SectorForest
