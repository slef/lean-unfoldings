module

public import Unfoldings.Cone.AngularInjective
public import Unfoldings.Geometry.ConvexCover

/-!
# Convex angular fans have the Euclidean sector metric

When the total angle is less than pi, the ordered closed pieces cover the
corresponding convex planar sector. The development is bijective onto that
sector. Its inverse is nonexpanding on each closed piece, hence on the whole
sector, proving exact distances rather than just nonoverlap.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

theorem faceImage_union_eq_sector (small : A.totalAngle < Real.pi) :
    (⋃ i, A.faceImage i) = planarSector A.totalAngle := by
  ext z
  constructor
  · intro inside
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp inside
    obtain ⟨r, θ, bounds, rfl⟩ := (A.mem_faceImage_iff i z).mp hi
    exact polar_mem_planarSector A.totalAngle r θ A.totalAngle_pos small r.coe_nonneg
      ⟨(A.heading_nonneg _).trans bounds.1, bounds.2.trans (A.heading_le_totalAngle _)⟩
  · intro inside
    obtain ⟨r, θ, bounds, equal⟩ :=
      (mem_planarSector_iff_polar A.totalAngle A.totalAngle_pos small z).mp inside
    obtain ⟨i, interval⟩ := A.exists_closed_heading_piece θ bounds
    exact Set.mem_iUnion.mpr ⟨i, (A.mem_faceImage_iff i z).mpr ⟨r, θ, interval, equal⟩⟩

theorem place_mem_sector (small : A.totalAngle < Real.pi) (i : Fin (n + 1)) (x : A.Cell i) :
    A.place i x ∈ planarSector A.totalAngle := by
  rw [← A.faceImage_union_eq_sector small]
  exact Set.mem_iUnion.mpr ⟨i, x.val, x.property, rfl⟩

theorem develop_mem_sector (small : A.totalAngle < Real.pi) (z : A.Surface) :
    A.develop z ∈ planarSector A.totalAngle := by
  obtain ⟨⟨i, x⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue z
  exact A.place_mem_sector small i x

def sectorEquiv (small : A.totalAngle < Real.pi) :
    A.Surface ≃ planarSector A.totalAngle :=
  Equiv.ofBijective (fun z => ⟨A.develop z, A.develop_mem_sector small z⟩) (by
    constructor
    · intro z w equal
      apply A.develop_injective_of_lt_full (small.trans (by linarith [Real.pi_pos]))
      exact congrArg Subtype.val equal
    · intro z
      have inside : z.val ∈ ⋃ i, A.faceImage i := by
        rw [A.faceImage_union_eq_sector small]
        exact z.property
      obtain ⟨i, x, hx, equal⟩ := Set.mem_iUnion.mp inside
      exact ⟨A.faceMap i ⟨x, hx⟩, Subtype.ext equal⟩)

@[simp] theorem sectorEquiv_apply (small : A.totalAngle < Real.pi) (z : A.Surface) :
    (A.sectorEquiv small z).val = A.develop z := rfl

theorem sectorEquiv_symm_place (small : A.totalAngle < Real.pi)
    (i : Fin (n + 1)) (x : A.Cell i) (inside : A.place i x ∈ planarSector A.totalAngle) :
    (A.sectorEquiv small).symm ⟨A.place i x, inside⟩ = A.faceMap i x := by
  apply (A.sectorEquiv small).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext rfl

theorem sectorEquiv_symm_lipschitz (small : A.totalAngle < Real.pi) :
    LipschitzWith 1 (A.sectorEquiv small).symm := by
  let domain := planarSector A.totalAngle
  let inverse := (A.sectorEquiv small).symm
  let pieces (i : Fin (n + 1)) : Set domain := Subtype.val ⁻¹' A.faceImage i
  have closed (i : Fin (n + 1)) : IsClosed (pieces i) :=
    ((rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph.isClosedMap _
      (isClosed_planarSector (A.angle i)
        (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne')).preimage
          continuous_subtype_val
  have cover : ⋃ i, pieces i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have inside : z.val ∈ ⋃ i, A.faceImage i := by
      rw [A.faceImage_union_eq_sector small]
      exact z.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp inside
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have bounded (i : Fin (n + 1)) : LipschitzOnWith 1 inverse (pieces i) := by
    intro z hz w hw
    obtain ⟨left_point, hl, left_equal⟩ := hz
    obtain ⟨right_point, hr, right_equal⟩ := hw
    let x : A.Cell i := ⟨left_point, hl⟩
    let y : A.Cell i := ⟨right_point, hr⟩
    have left_coordinates : A.place i x = z.val := left_equal
    have right_coordinates : A.place i y = w.val := right_equal
    have left_preimage : inverse z = A.faceMap i x := by
      apply (A.sectorEquiv small).injective
      exact (Equiv.apply_symm_apply _ z).trans (Subtype.ext left_coordinates.symm)
    have right_preimage : inverse w = A.faceMap i y := by
      apply (A.sectorEquiv small).injective
      exact (Equiv.apply_symm_apply _ w).trans (Subtype.ext right_coordinates.symm)
    change edist (inverse z) (inverse w) ≤ (1 : ℝ≥0∞) * edist z.val w.val
    rw [one_mul, left_preimage, right_preimage, ← left_coordinates, ← right_coordinates]
    exact (A.faceMap_isometry i x y).trans (A.place_isometry i x y).symm |>.le
  exact convex_subtype_lipschitzWith_of_finite_closed_cover domain
    (convex_planarSector _) pieces closed cover inverse 1 bounded

theorem sectorEquiv_isometry (small : A.totalAngle < Real.pi) :
    Isometry (A.sectorEquiv small) := by
  intro x y
  apply le_antisymm
  · exact (A.develop_lipschitz.edist_le_mul x y).trans_eq (by simp)
  · have bound := (A.sectorEquiv_symm_lipschitz small).edist_le_mul
      (A.sectorEquiv small x) (A.sectorEquiv small y)
    simpa only [Equiv.symm_apply_apply, ENNReal.coe_one, one_mul] using bound

/-- The slit fan metric agrees with the Euclidean chord metric throughout
a convex sector of total angle less than pi. -/
def sectorIsometry (small : A.totalAngle < Real.pi) :
    A.Surface ≃ᵢ planarSector A.totalAngle :=
  ⟨A.sectorEquiv small, A.sectorEquiv_isometry small⟩

end Unfoldings.AngularFan
