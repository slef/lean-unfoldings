module

public import Unfoldings.Cone.AngularFibers
public import Unfoldings.Metric.ConvexCover

/-! Closing the two actual outer banks of a full-turn slit fan gives the Euclidean plane metric. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

/-- Only the two original outer banks are newly identified, at the same actual radius. -/
def closingRelation (x y : MetricGluing.Total (fun _ : Unit => A.Surface)) : Prop :=
  ∃ r : ℝ≥0, x.2 = A.faceMap (Fin.last n) (A.finish (Fin.last n) r) ∧
    y.2 = A.faceMap 0 (A.start 0 r)

abbrev ClosedSurface := MetricGluing.Realization (fun _ : Unit => A.Surface) A.closingRelation

/-- The original slit fan, with only its outer banks restored. -/
def closeMap : A.Surface → A.ClosedSurface :=
  MetricGluing.of (fun _ : Unit => A.Surface) A.closingRelation ()

theorem closeMap_lipschitz : LipschitzWith 1 A.closeMap :=
  MetricGluing.of_lipschitz _ _ _

theorem closeMap_outer_banks (r : ℝ≥0) :
    A.closeMap (A.faceMap (Fin.last n) (A.finish (Fin.last n) r)) =
      A.closeMap (A.faceMap 0 (A.start 0 r)) :=
  MetricGluing.point_eq_of_glue _ ⟨r, rfl, rfl⟩

/-- At a full turn, the actual original developments descend across the new bank seam. -/
def closedDevelop (full : A.totalAngle = 2 * Real.pi) : A.ClosedSurface → ℂ :=
  MetricGluing.lift (fun _ : Unit => A.Surface) A.closingRelation (fun _ => A.develop)
    (fun _ => A.develop_lipschitz)
    (by
      rintro x y ⟨r, first, last⟩
      rw [first, last, A.develop_faceMap, A.develop_faceMap]
      exact A.outer_banks_coincide full r)

@[simp] theorem closedDevelop_closeMap (full : A.totalAngle = 2 * Real.pi) (x : A.Surface) :
    A.closedDevelop full (A.closeMap x) = A.develop x := rfl

theorem closedDevelop_lipschitz (full : A.totalAngle = 2 * Real.pi) :
    LipschitzWith 1 (A.closedDevelop full) := MetricGluing.lift_lipschitz _ _ _ _ _

theorem closedDevelop_injective (full : A.totalAngle = 2 * Real.pi) :
    Function.Injective (A.closedDevelop full) := by
  intro x y equal
  obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective _ A.closingRelation x
  obtain ⟨⟨j, q⟩, rfl⟩ := MetricGluing.point_surjective _ A.closingRelation y
  cases i
  cases j
  change A.develop p = A.develop q at equal
  rcases A.develop_fiber_cases full p q equal with same | ⟨r, pair⟩
  · subst q
    rfl
  · rcases pair with ⟨first, last⟩ | ⟨last, first⟩
    · rw [first, last]
      exact (A.closeMap_outer_banks r).symm
    · rw [last, first]
      exact A.closeMap_outer_banks r

theorem closedDevelop_surjective (full : A.totalAngle = 2 * Real.pi) :
    Function.Surjective (A.closedDevelop full) := by
  intro z
  obtain ⟨x, equal⟩ := A.develop_surjective_of_full full z
  exact ⟨A.closeMap x, equal⟩

/-- The underlying bijection is constructed from the actual bank quotient. -/
def closedPlaneEquiv (full : A.totalAngle = 2 * Real.pi) : A.ClosedSurface ≃ ℂ :=
  Equiv.ofBijective (A.closedDevelop full)
    ⟨A.closedDevelop_injective full, A.closedDevelop_surjective full⟩

/-- The finite closed cell images cover the plane and bound the inverse across cells. -/
theorem closedPlaneEquiv_symm_lipschitz (full : A.totalAngle = 2 * Real.pi) :
    LipschitzWith 1 (A.closedPlaneEquiv full).symm := by
  let inverse := (A.closedPlaneEquiv full).symm
  let g : ↥(Set.univ : Set ℂ) → A.ClosedSurface := fun z => inverse z.val
  let pieces (i : Fin (n + 1)) : Set (Set.univ : Set ℂ) := {z | z.val ∈ A.faceImage i}
  have closed (i : Fin (n + 1)) : IsClosed (pieces i) :=
    ((rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph.isClosedMap _
      (isClosed_planarSector (A.angle i)
        (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne')).preimage
          continuous_subtype_val
  have cover : (⋃ i, pieces i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have member : z.val ∈ ⋃ i, A.faceImage i := by rw [A.faceImage_cover_of_full full]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have piece_bound (i : Fin (n + 1)) : LipschitzOnWith 1 g (pieces i) := by
    intro z hz w hw
    obtain ⟨p, hp, first⟩ := hz
    obtain ⟨q, hq, last⟩ := hw
    change A.place i ⟨p, hp⟩ = z.val at first
    change A.place i ⟨q, hq⟩ = w.val at last
    have at_z : g z = A.closeMap (A.faceMap i ⟨p, hp⟩) := by
      apply (A.closedPlaneEquiv full).injective
      exact ((A.closedPlaneEquiv full).apply_symm_apply z.val).trans first.symm
    have at_w : g w = A.closeMap (A.faceMap i ⟨q, hq⟩) := by
      apply (A.closedPlaneEquiv full).injective
      exact ((A.closedPlaneEquiv full).apply_symm_apply w.val).trans last.symm
    rw [at_z, at_w]
    simp only [ENNReal.coe_one, one_mul]
    have bound := A.closeMap_lipschitz (A.faceMap i ⟨p, hp⟩) (A.faceMap i ⟨q, hq⟩)
    simp only [ENNReal.coe_one, one_mul] at bound
    calc
      _ ≤ edist (A.faceMap i ⟨p, hp⟩) (A.faceMap i ⟨q, hq⟩) := bound
      _ = edist z w := by
        rw [A.faceMap_isometry i, ← (A.place_isometry i).edist_eq, first, last]
        rfl
  have bounded := convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
    Set.univ convex_univ pieces closed cover g 1 piece_bound
  intro z w
  exact bounded ⟨z, Set.mem_univ z⟩ ⟨w, Set.mem_univ w⟩

/-- Closing a genuine full-turn fan gives the exact complete Euclidean plane metric. -/
def closedPlaneIsometryEquiv (full : A.totalAngle = 2 * Real.pi) : A.ClosedSurface ≃ᵢ ℂ where
  toEquiv := A.closedPlaneEquiv full
  isometry_toFun := by
    intro x y
    change edist (A.closedPlaneEquiv full x) (A.closedPlaneEquiv full y) = edist x y
    apply le_antisymm
    · change edist (A.closedDevelop full x) (A.closedDevelop full y) ≤ edist x y
      simpa only [ENNReal.coe_one, one_mul] using A.closedDevelop_lipschitz full x y
    · have bound := A.closedPlaneEquiv_symm_lipschitz full
        (A.closedPlaneEquiv full x) (A.closedPlaneEquiv full y)
      simpa only [Equiv.symm_apply_apply, ENNReal.coe_one, one_mul] using bound

end Unfoldings.AngularFan
