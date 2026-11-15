module

public import Unfoldings.Cone.AngularInjective
public import Unfoldings.Metric.PolygonalPiecewise

/-! Reentrant slit fans have exactly the intrinsic polygonal metric of their actual planar image. -/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Unfoldings.AngularFan

variable {n : ℕ} (A : AngularFan n)

/-- The actual closed sector images, allowing total widths larger than a half-turn. -/
def planarRegion : Set ℂ := ⋃ i, A.faceImage i

theorem isClosed_faceImage (i : Fin (n + 1)) : IsClosed (A.faceImage i) :=
  (rotation (Circle.exp (A.heading i.castSucc))).toHomeomorph.isClosedMap _
    (isClosed_planarSector (A.angle i)
      (Real.sin_pos_of_pos_of_lt_pi (A.positive i) (A.small i)).ne')

theorem convex_faceImage (i : Fin (n + 1)) : Convex ℝ (A.faceImage i) := by
  exact (convex_planarSector (A.angle i)).linear_image
    (rotation (Circle.exp (A.heading i.castSucc))).toLinearMap

theorem place_mem_planarRegion (i : Fin (n + 1)) (x : A.Cell i) :
    A.place i x ∈ A.planarRegion := Set.mem_iUnion.mpr ⟨i, x.val, x.property, rfl⟩

/-- A genuine original cell, mapped into the intrinsic region rather than its ambient subspace. -/
def regionCell (i : Fin (n + 1)) (x : A.Cell i) : PolygonalPoint A.planarRegion :=
  ⟨A.place i x, A.place_mem_planarRegion i x⟩

theorem regionCell_isometry (i : Fin (n + 1)) : Isometry (A.regionCell i) := by
  intro x y
  have segment_inside : segment ℝ (A.place i x) (A.place i y) ⊆ A.planarRegion :=
    ((A.convex_faceImage i).segment_subset ⟨x.val, x.property, rfl⟩
      ⟨y.val, y.property, rfl⟩).trans (Set.subset_iUnion _ i)
  exact (PolygonalPoint.edist_eq_of_segment segment_inside).trans (A.place_isometry i x y)

def regionDevelop : A.Surface → PolygonalPoint A.planarRegion :=
  MetricGluing.lift A.Cell A.glue A.regionCell (fun i => (A.regionCell_isometry i).lipschitzWith)
    (fun a b joined => PolygonalPoint.ext (A.place_compatible a b joined))

theorem regionDevelop_lipschitz : LipschitzWith 1 A.regionDevelop :=
  MetricGluing.lift_lipschitz _ _ _ _ _

@[simp] theorem regionDevelop_faceMap (i : Fin (n + 1)) (x : A.Cell i) :
    A.regionDevelop (A.faceMap i x) = A.regionCell i x := rfl

@[simp] theorem regionDevelop_val (x : A.Surface) : (A.regionDevelop x).val = A.develop x := by
  obtain ⟨⟨i, p⟩, rfl⟩ := MetricGluing.point_surjective A.Cell A.glue x
  rfl

def intrinsicRegionEquiv (small : A.totalAngle < 2 * Real.pi) :
    A.Surface ≃ PolygonalPoint A.planarRegion :=
  Equiv.ofBijective A.regionDevelop (by
    constructor
    · intro x y equal
      apply A.develop_injective_of_lt_full small
      simpa only [regionDevelop_val] using congrArg PolygonalPoint.val equal
    · intro y
      obtain ⟨i, z, hz, equal⟩ := Set.mem_iUnion.mp y.property
      exact ⟨A.faceMap i ⟨z, hz⟩, PolygonalPoint.ext equal⟩)

theorem intrinsicRegionEquiv_symm_lipschitz (small : A.totalAngle < 2 * Real.pi) :
    LipschitzWith 1 (A.intrinsicRegionEquiv small).symm := by
  let f : A.planarRegion → A.Surface := fun z =>
    (A.intrinsicRegionEquiv small).symm (PolygonalPoint.ofSubtype z)
  have bounded (i : Fin (n + 1)) : LipschitzOnWith 1 f {z | z.val ∈ A.faceImage i} := by
    intro z hz w hw
    obtain ⟨p, hp, first⟩ := hz
    obtain ⟨q, hq, last⟩ := hw
    change A.place i ⟨p, hp⟩ = z.val at first
    change A.place i ⟨q, hq⟩ = w.val at last
    have at_z : f z = A.faceMap i ⟨p, hp⟩ := by
      apply (A.intrinsicRegionEquiv small).injective
      exact ((A.intrinsicRegionEquiv small).apply_symm_apply _).trans
        (PolygonalPoint.ext first.symm)
    have at_w : f w = A.faceMap i ⟨q, hq⟩ := by
      apply (A.intrinsicRegionEquiv small).injective
      exact ((A.intrinsicRegionEquiv small).apply_symm_apply _).trans
        (PolygonalPoint.ext last.symm)
    rw [at_z, at_w]
    simp only [ENNReal.coe_one, one_mul]
    calc
      _ = edist (A.place i ⟨p, hp⟩) (A.place i ⟨q, hq⟩) :=
        (A.faceMap_isometry i _ _).trans (A.place_isometry i _ _).symm
      _ ≤ edist z w := by rw [first, last]; exact le_rfl
  exact PolygonalPoint.lipschitz_of_finite_closed_cover A.faceImage A.isClosed_faceImage
    (Set.Subset.refl A.planarRegion) f bounded

/-- This includes genuine reentrant sectors: distances are intrinsic polygonal distances.
Only reaching a full turn requires the additional outer-bank identification. -/
def intrinsicRegionIsometryEquiv (small : A.totalAngle < 2 * Real.pi) :
    A.Surface ≃ᵢ PolygonalPoint A.planarRegion where
  toEquiv := A.intrinsicRegionEquiv small
  isometry_toFun := by
    intro x y
    change edist (A.regionDevelop x) (A.regionDevelop y) = edist x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using A.regionDevelop_lipschitz x y
    · change edist x y ≤ edist (A.intrinsicRegionEquiv small x) (A.intrinsicRegionEquiv small y)
      have bound := A.intrinsicRegionEquiv_symm_lipschitz small
        (A.intrinsicRegionEquiv small x) (A.intrinsicRegionEquiv small y)
      simpa only [Equiv.symm_apply_apply, ENNReal.coe_one, one_mul] using bound

@[simp] theorem intrinsicRegionIsometryEquiv_val (small : A.totalAngle < 2 * Real.pi)
    (x : A.Surface) : (A.intrinsicRegionIsometryEquiv small x).val = A.develop x :=
  A.regionDevelop_val x

end Unfoldings.AngularFan
