module

public import Unfoldings.Cone.SpatialConvexLift

/-!
# Piecewise rigid spatial parametrizations determine the intrinsic metric

A finite closed convex partition of the plane, rigidly mapped onto the actual
spatial tangent image, supplies an intrinsic isometry. Both metric bounds are
proved from the route metric: the spatial inverse is isometric on each convex
piece, and the inverse planar coordinates descend through the tangent gluing.
-/

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (v : C.Vertex Set.univ)

/-- Geometric data for a finite piecewise rigid parametrization of the spatial fan.
No assertion about the intrinsic metric is included. -/
structure TangentParametrization where
  count : ℕ
  pieces : Fin count → Set Plane
  closed : ∀ i, IsClosed (pieces i)
  convex : ∀ i, Convex ℝ (pieces i)
  cover : ⋃ i, pieces i = Set.univ
  place : Fin count → Plane →ᵃⁱ[ℝ] Space
  map : Plane → Space
  agrees : ∀ i, ∀ z ∈ pieces i, map z = place i z
  injective : Function.Injective map
  range_eq : Set.range map = Set.range (F.tangentToSpace Set.univ v)

namespace TangentParametrization

variable {F v} (A : F.TangentParametrization v)

def lift : Plane → C.TangentFan Set.univ v := fun z =>
  F.tangentLiftSpatial v (Set.range (F.tangentToSpace Set.univ v)) (fun _ h => h)
    ⟨A.map z, A.range_eq.le ⟨z, rfl⟩⟩

@[simp] theorem spatial_lift (z : Plane) :
    F.tangentToSpace Set.univ v (A.lift z) = A.map z :=
  F.tangentToSpace_liftSpatial _ _ _ _

theorem lift_lipschitz (embedded : F.IsEmbedded) : LipschitzWith 1 A.lift := by
  have bounded (i : Fin A.count) : LipschitzOnWith 1 A.lift (A.pieces i) := by
    let s := A.place i '' A.pieces i
    have inside : s ⊆ Set.range (F.tangentToSpace Set.univ v) := by
      rintro _ ⟨z, hz, rfl⟩
      exact A.range_eq.le ⟨z, A.agrees i z hz⟩
    have iso := F.tangentLiftSpatial_isometry v embedded s
      ((A.convex i).affine_image (A.place i).toAffineMap) inside
    intro x hx y hy
    let p : s := ⟨A.place i x, ⟨x, hx, rfl⟩⟩
    let q : s := ⟨A.place i y, ⟨y, hy, rfl⟩⟩
    have first : A.lift x = F.tangentLiftSpatial v s inside p := by
      apply F.tangentToSpace_injective embedded v
      rw [A.spatial_lift, F.tangentToSpace_liftSpatial]
      exact A.agrees i x hx
    have last : A.lift y = F.tangentLiftSpatial v s inside q := by
      apply F.tangentToSpace_injective embedded v
      rw [A.spatial_lift, F.tangentToSpace_liftSpatial]
      exact A.agrees i y hy
    simp only [ENNReal.coe_one, one_mul]
    rw [first, last, iso.edist_eq]
    exact ((A.place i).isometry x y).le
  exact lipschitzOnWith_univ.mp (convex_lipschitzOnWith_of_finite_closed_cover
    Set.univ convex_univ A.pieces A.closed (by rw [A.cover]) A.lift 1 bounded)

def inverse : C.TangentFan Set.univ v → Plane := fun z =>
  Classical.choose (A.range_eq.ge (Set.mem_range_self z))

@[simp] theorem map_inverse (z : C.TangentFan Set.univ v) :
    A.map (A.inverse z) = F.tangentToSpace Set.univ v z :=
  Classical.choose_spec (A.range_eq.ge (Set.mem_range_self z))

@[simp] theorem inverse_lift (z : Plane) : A.inverse (A.lift z) = z :=
  A.injective ((A.map_inverse _).trans (A.spatial_lift z))

@[simp] theorem lift_inverse (embedded : F.IsEmbedded) (z : C.TangentFan Set.univ v) :
    A.lift (A.inverse z) = z := by
  apply F.tangentToSpace_injective embedded v
  rw [A.spatial_lift, A.map_inverse]

theorem inverse_cell_lipschitz (c : C.CornerAt Set.univ v) :
    LipschitzWith 1 (A.inverse ∘ C.tangentFaceMap Set.univ v c) := by
  let pieces (i : Fin A.count) : Set (C.TangentCell Set.univ v c) :=
    (F.tangentCellToSpace Set.univ v c) ⁻¹' (A.place i '' A.pieces i)
  have closed (i : Fin A.count) : IsClosed (pieces i) :=
    ((A.place i).isometry.isClosedEmbedding.isClosedMap _ (A.closed i)).preimage
      (F.tangentCellToSpace_isometry Set.univ v c).continuous
  have cover : ⋃ i, pieces i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let z := A.inverse (C.tangentFaceMap Set.univ v c x)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (A.cover.ge (Set.mem_univ z))
    refine Set.mem_iUnion.mpr ⟨i, z, hi, ?_⟩
    exact (A.agrees i z hi).symm.trans (A.map_inverse _)
  have bounded (i : Fin A.count) :
      LipschitzOnWith 1 (A.inverse ∘ C.tangentFaceMap Set.univ v c) (pieces i) := by
    intro x hx y hy
    obtain ⟨p, hp, first⟩ := hx
    obtain ⟨q, hq, last⟩ := hy
    have at_x : A.inverse (C.tangentFaceMap Set.univ v c x) = p :=
      A.injective ((A.map_inverse _).trans (first.symm.trans (A.agrees i p hp).symm))
    have at_y : A.inverse (C.tangentFaceMap Set.univ v c y) = q :=
      A.injective ((A.map_inverse _).trans (last.symm.trans (A.agrees i q hq).symm))
    change edist (A.inverse (C.tangentFaceMap Set.univ v c x))
      (A.inverse (C.tangentFaceMap Set.univ v c y)) ≤ (1 : ℝ≥0∞) * edist x y
    rw [one_mul, at_x, at_y, ← (A.place i).isometry.edist_eq p q, first, last]
    exact ((F.tangentCellToSpace_isometry Set.univ v c) x y).le
  exact convex_subtype_lipschitzWith_of_finite_closed_cover
    ((C.triangle c.val.1).cornerWedge c.val.2)
    ((C.triangle c.val.1).convex_cornerWedge c.val.2) pieces closed cover
    (A.inverse ∘ C.tangentFaceMap Set.univ v c) 1 bounded

theorem inverse_lipschitz : LipschitzWith 1 A.inverse := by
  let cells := fun c => A.inverse ∘ C.tangentFaceMap Set.univ v c
  have compatible : ∀ a b, C.tangentGlue Set.univ v a b →
      cells a.1 a.2 = cells b.1 b.2 := by
    intro a b related
    exact congrArg A.inverse (MetricGluing.point_eq_of_glue _ related)
  let descended := MetricGluing.lift (C.TangentCell Set.univ v)
    (C.tangentGlue Set.univ v) cells A.inverse_cell_lipschitz compatible
  have equal : A.inverse = descended :=
    MetricGluing.lift_unique _ _ cells A.inverse_cell_lipschitz compatible A.inverse
      (fun _ _ => rfl)
  rw [equal]
  exact MetricGluing.lift_lipschitz _ _ cells A.inverse_cell_lipschitz compatible

theorem lift_isometry (embedded : F.IsEmbedded) : Isometry A.lift := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using (A.lift_lipschitz embedded).edist_le_mul x y
  · simpa only [A.inverse_lift, ENNReal.coe_one, one_mul] using
      A.inverse_lipschitz.edist_le_mul (A.lift x) (A.lift y)

/-- The intrinsic Euclidean isometry is a consequence of the geometric parametrization. -/
def isometryEquiv (embedded : F.IsEmbedded) : Plane ≃ᵢ C.TangentFan Set.univ v :=
  ⟨⟨A.lift, A.inverse, A.inverse_lift, A.lift_inverse embedded⟩, A.lift_isometry embedded⟩

end TangentParametrization
end Unfoldings.SpatialFolding
