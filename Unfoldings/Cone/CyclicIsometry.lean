module

public import Unfoldings.Cone.CyclicDevelopment
public import Unfoldings.Cone.AngularFibers
public import Unfoldings.Geometry.ConvexCover

/-!
# Full-turn cyclic tangent fans are Euclidean planes

The only extra fibers of the slit development are the outer banks, which
the actual cyclic seam identifies. The resulting development is bijective.
Its inverse is nonexpanding on every closed sector piece; the finite
closed-cover theorem gives the same bound on the whole convex plane.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

theorem cyclicDevelopment_linkCell {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (i : Fin (n + 1)) (x : (C.linkAngularFan retain v chain).Cell i) :
    C.cyclicDevelopment retain v chain covers closes full
      (C.linkCellToTangent retain v chain i x) = (C.linkAngularFan retain v chain).place i x := by
  have image := C.cyclicDevelopment_angularToTangent retain v chain covers closes full
    ((C.linkAngularFan retain v chain).faceMap i x)
  rw [C.angularToTangent_faceMap, AngularFan.develop_faceMap] at image
  exact image

theorem cyclicDevelopment_injective {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    Function.Injective (C.cyclicDevelopment retain v chain covers closes full) := by
  intro z w image
  obtain ⟨a, rfl⟩ := C.angularToTangent_surjective retain v chain covers z
  obtain ⟨b, rfl⟩ := C.angularToTangent_surjective retain v chain covers w
  simp only [C.cyclicDevelopment_angularToTangent] at image
  rcases (C.linkAngularFan retain v chain).develop_fiber_cases full a b image with same | ⟨r, banks⟩
  · exact congrArg (C.angularToTangent retain v chain) same
  · rcases banks with ⟨left, right⟩ | ⟨left, right⟩
    · rw [left, right]
      exact (C.angularToTangent_outer_banks retain v chain closes r).symm
    · rw [left, right]
      exact C.angularToTangent_outer_banks retain v chain closes r

def cyclicEquiv {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    C.TangentFan retain v ≃ ℂ :=
  Equiv.ofBijective (C.cyclicDevelopment retain v chain covers closes full)
    ⟨C.cyclicDevelopment_injective retain v chain covers closes full,
      C.cyclicDevelopment_surjective retain v chain covers closes full⟩

theorem cyclicEquiv_symm_place {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (i : Fin (n + 1)) (x : (C.linkAngularFan retain v chain).Cell i) :
    (C.cyclicEquiv retain v chain covers closes full).symm
      ((C.linkAngularFan retain v chain).place i x) = C.linkCellToTangent retain v chain i x := by
  apply (C.cyclicEquiv retain v chain covers closes full).injective
  rw [Equiv.apply_symm_apply]
  exact (C.cyclicDevelopment_linkCell retain v chain covers closes full i x).symm

theorem cyclicEquiv_symm_lipschitz {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    LipschitzWith 1 (C.cyclicEquiv retain v chain covers closes full).symm := by
  let A := C.linkAngularFan retain v chain
  let inverse := (C.cyclicEquiv retain v chain covers closes full).symm
  have closed (i : Fin (n + 1)) : IsClosed (A.faceImage i) :=
    (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph.isClosedMap _
      (isClosed_planarSector (A.angle i)
        (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne')
  have pieces (i : Fin (n + 1)) : LipschitzOnWith 1 inverse (A.faceImage i) := by
    intro z hz w hw
    obtain ⟨left_point, hl, rfl⟩ := hz
    obtain ⟨right_point, hr, rfl⟩ := hw
    let x : A.Cell i := ⟨left_point, hl⟩
    let y : A.Cell i := ⟨right_point, hr⟩
    change edist (inverse (A.place i x)) (inverse (A.place i y)) ≤
      (1 : ℝ≥0∞) * edist (A.place i x) (A.place i y)
    rw [one_mul]
    change edist ((C.cyclicEquiv retain v chain covers closes full).symm (A.place i x))
      ((C.cyclicEquiv retain v chain covers closes full).symm (A.place i y)) ≤ _
    rw [C.cyclicEquiv_symm_place, C.cyclicEquiv_symm_place]
    have bound := (C.linkCellToTangent_lipschitz retain v chain i).edist_le_mul x y
    simp only [ENNReal.coe_one, one_mul] at bound
    exact bound.trans_eq (A.place_isometry i x y).symm
  have cover : Set.univ ⊆ ⋃ i, A.faceImage i := by
    rw [A.faceImage_cover_of_full full]
  have global := convex_lipschitzOnWith_of_finite_closed_cover Set.univ convex_univ
    A.faceImage closed cover inverse 1 pieces
  intro x y
  exact global (Set.mem_univ x) (Set.mem_univ y)

theorem cyclicDevelopment_isometry {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    Isometry (C.cyclicDevelopment retain v chain covers closes full) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (C.cyclicDevelopment_lipschitz retain v chain covers closes full).edist_le_mul x y
  · let e := C.cyclicEquiv retain v chain covers closes full
    have bound := (C.cyclicEquiv_symm_lipschitz retain v chain covers closes full).edist_le_mul
      (e x) (e y)
    rw [e.symm_apply_apply, e.symm_apply_apply, ENNReal.coe_one, one_mul] at bound
    exact bound

/-- A full-turn actual cyclic tangent fan has exactly the Euclidean plane metric. -/
def cyclicFanIsometry {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi) :
    C.TangentFan retain v ≃ᵢ ℂ :=
  ⟨C.cyclicEquiv retain v chain covers closes full,
    C.cyclicDevelopment_isometry retain v chain covers closes full⟩

@[simp] theorem cyclicFanIsometry_apply {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (closes : C.linkMate retain v (C.linkTurn retain v chain.last) = chain.first)
    (full : (C.linkAngularFan retain v chain).totalAngle = 2 * Real.pi)
    (z : C.TangentFan retain v) :
    C.cyclicFanIsometry retain v chain covers closes full z =
      C.cyclicDevelopment retain v chain covers closes full z := rfl

theorem exists_flatFanIsometry (interior : ¬ C.IsBoundaryVertex retain v)
    (flat : C.totalAngle retain v = 2 * Real.pi) :
    Nonempty (C.TangentFan retain v ≃ᵢ ℂ) := by
  obtain ⟨n, chain, closes, covers⟩ := C.exists_cyclic_link retain v interior
  exact ⟨C.cyclicFanIsometry retain v chain covers closes
    ((C.linkAngularFan_totalAngle retain v chain covers).trans flat)⟩

theorem exists_flatFanIsometry_origin (interior : ¬ C.IsBoundaryVertex retain v)
    (flat : C.totalAngle retain v = 2 * Real.pi) :
    ∃ e : C.TangentFan retain v ≃ᵢ ℂ, e (C.tangentOrigin retain v) = 0 := by
  obtain ⟨n, chain, closes, covers⟩ := C.exists_cyclic_link retain v interior
  let full := (C.linkAngularFan_totalAngle retain v chain covers).trans flat
  exact ⟨C.cyclicFanIsometry retain v chain covers closes full,
    C.cyclicDevelopment_origin retain v chain covers closes full⟩

end Unfoldings.TriangleComplex
