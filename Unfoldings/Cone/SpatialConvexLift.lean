module

public import Unfoldings.Cone.SpatialEmbedding
public import Unfoldings.Geometry.ConvexCover

/-!
# Isometric inverse tangent folding on convex spatial subsets

The actual embedded tangent fan has finitely many closed isometric wedge
images. Its spatial inverse is therefore nonexpanding on every convex subset
of its image. Ambient nonexpansion gives the reverse bound and hence an
isometry, even across arbitrarily many coplanar wedge subdivisions.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (v : C.Vertex Set.univ)

def tangentLiftSpatial (s : Set Space) (inside : s ⊆ Set.range (F.tangentToSpace Set.univ v)) :
    s → C.TangentFan Set.univ v := fun x => Classical.choose (inside x.property)

@[simp] theorem tangentToSpace_liftSpatial (s : Set Space)
    (inside : s ⊆ Set.range (F.tangentToSpace Set.univ v)) (x : s) :
    F.tangentToSpace Set.univ v (F.tangentLiftSpatial v s inside x) = x.val :=
  Classical.choose_spec (inside x.property)

theorem tangentLiftSpatial_lipschitz (embedded : F.IsEmbedded) (s : Set Space)
    (convex : Convex ℝ s) (inside : s ⊆ Set.range (F.tangentToSpace Set.univ v)) :
    LipschitzWith 1 (F.tangentLiftSpatial v s inside) := by
  let pieces (c : C.CornerAt Set.univ v) : Set s := Subtype.val ⁻¹'
    (F.place c.val.1 '' (C.triangle c.val.1).cornerWedge c.val.2)
  have closed (c : C.CornerAt Set.univ v) : IsClosed (pieces c) :=
    ((F.place c.val.1).isometry.isClosedEmbedding.isClosedMap _
      ((C.triangle c.val.1).isClosed_cornerWedge c.val.2)).preimage continuous_subtype_val
  have cover : ⋃ c, pieces c = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨w, image⟩ := inside x.property
    obtain ⟨⟨c, p⟩, rfl⟩ := MetricGluing.point_surjective
      (C.TangentCell Set.univ v) (C.tangentGlue Set.univ v) w
    exact Set.mem_iUnion.mpr ⟨c, p.val, p.property, image⟩
  have bounded (c : C.CornerAt Set.univ v) :
      LipschitzOnWith 1 (F.tangentLiftSpatial v s inside) (pieces c) := by
    intro z hz w hw
    obtain ⟨left, hl, left_equal⟩ := hz
    obtain ⟨right, hr, right_equal⟩ := hw
    let x : C.TangentCell Set.univ v c := ⟨left, hl⟩
    let y : C.TangentCell Set.univ v c := ⟨right, hr⟩
    have first : F.tangentLiftSpatial v s inside z = C.tangentFaceMap Set.univ v c x := by
      apply F.tangentToSpace_injective embedded v
      rw [F.tangentToSpace_liftSpatial, F.tangentToSpace_faceMap]
      exact left_equal.symm
    have last : F.tangentLiftSpatial v s inside w = C.tangentFaceMap Set.univ v c y := by
      apply F.tangentToSpace_injective embedded v
      rw [F.tangentToSpace_liftSpatial, F.tangentToSpace_faceMap]
      exact right_equal.symm
    change edist (F.tangentLiftSpatial v s inside z) (F.tangentLiftSpatial v s inside w) ≤
      (1 : ℝ≥0∞) * edist z.val w.val
    rw [one_mul, first, last, ← left_equal, ← right_equal]
    exact ((F.tangentFaceMap_isometry Set.univ v c x y).trans
      (F.tangentCellToSpace_isometry Set.univ v c x y).symm).le
  exact convex_subtype_lipschitzWith_of_finite_closed_cover s convex pieces closed cover
    (F.tangentLiftSpatial v s inside) 1 bounded

theorem tangentLiftSpatial_isometry (embedded : F.IsEmbedded) (s : Set Space)
    (convex : Convex ℝ s) (inside : s ⊆ Set.range (F.tangentToSpace Set.univ v)) :
    Isometry (F.tangentLiftSpatial v s inside) := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using
      (F.tangentLiftSpatial_lipschitz v embedded s convex inside).edist_le_mul x y
  · have bound := (F.tangentToSpace_lipschitz Set.univ v).edist_le_mul
      (F.tangentLiftSpatial v s inside x) (F.tangentLiftSpatial v s inside y)
    change edist x.val y.val ≤ _
    simpa only [F.tangentToSpace_liftSpatial, ENNReal.coe_one, one_mul] using bound

end Unfoldings.SpatialFolding
