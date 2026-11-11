module

public import Unfoldings.Cap.ClipTrianglePartition

/-!
# Actual isometric spatial triangles covering the clipped roof

Pull each projected triangle back through its original support face's affine
projection. The resulting Euclidean triangle uses that face's actual spatial
isometry and normal. The whole roof clip is covered exactly and projected
interiors are disjoint. These are physical triangles, before conforming seam
pairings or an acute extension triangulation is constructed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- An arbitrary active point lifts to the actual original support plane. -/
theorem roofPoint_eq_support_placement (f : Face) {p : Plane}
    (active : K.roofHeight p = K.supportHeight f p) :
    K.roofPoint p = K.folding.place f ((K.projectFaceEquiv f).symm p) := by
  let x := (K.projectFaceEquiv f).symm p
  have projected : K.projectFace f x = p := (K.projectFaceEquiv f).apply_symm_apply p
  have height := K.supportHeight_face f x
  rw [projected, ← active] at height
  have horizontal : Cap.horizontal (K.folding.place f x) = p := projected
  ext i
  fin_cases i
  · exact (congrArg (fun p : Plane => p 0) horizontal).symm
  · exact (congrArg (fun p : Plane => p 1) horizontal).symm
  · exact height

structure ClipSpatialTriangles (Z : ℝ) where
  Index : Type
  finite : Finite Index
  projectedTriangle : Index → Triangle
  face : Index → Face
  cover : K.clipFootprint Z = ⋃ i, (projectedTriangle i).carrier
  separated : Pairwise (fun i j =>
    Disjoint (interior (projectedTriangle i).carrier) (interior (projectedTriangle j).carrier))
  active : ∀ i, ∀ p ∈ (projectedTriangle i).carrier,
    K.roofHeight p = K.supportHeight (face i) p

def clipSpatialTriangles {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) : K.ClipSpatialTriangles Z :=
  Classical.choice (by
    obtain ⟨I, finite, triangle, face, cover, separated, active⟩ :=
      K.exists_clip_triangle_partition member positive lower
    exact ⟨⟨I, finite, triangle, face, cover, separated, active⟩⟩)

namespace ClipSpatialTriangles

variable {K} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

/-- The actual Euclidean triangle in its original supporting plane's local coordinates. -/
def triangle (i : T.Index) : Triangle :=
  (T.projectedTriangle i).affineImage (K.projectFaceEquiv (T.face i)).symm.toAffineMap
    (K.projectFaceEquiv (T.face i)).symm.injective

theorem triangle_carrier (i : T.Index) : (T.triangle i).carrier =
    (K.projectFaceEquiv (T.face i)).symm '' (T.projectedTriangle i).carrier :=
  (T.projectedTriangle i).affineImage_carrier
    (K.projectFaceEquiv (T.face i)).symm.toAffineMap
    (K.projectFaceEquiv (T.face i)).symm.injective

def placement (i : T.Index) : Plane →ᵃⁱ[ℝ] Space := K.folding.place (T.face i)

def normal (i : T.Index) : Space := K.normal (T.face i)

theorem horizontal_placement (i : T.Index) (x : Plane) :
    Cap.horizontal (T.placement i x) = K.projectFace (T.face i) x := rfl

/-- Whole local triangles lift to the real extended roof, including their closed boundaries. -/
theorem placement_eq_roofPoint (i : T.Index) {x : Plane} (member : x ∈ (T.triangle i).carrier) :
    T.placement i x = K.roofPoint (K.projectFace (T.face i) x) := by
  rw [T.triangle_carrier] at member
  obtain ⟨p, member, rfl⟩ := member
  have projected := (K.projectFaceEquiv (T.face i)).apply_symm_apply p
  change K.projectFace (T.face i) ((K.projectFaceEquiv (T.face i)).symm p) = p at projected
  rw [projected]
  exact (K.roofPoint_eq_support_placement (T.face i) (T.active i p member)).symm

/-- Exact spatial coverage uses the original rigid supporting-face maps. -/
theorem spatial_cover : K.clippedRoof Z = ⋃ i, T.placement i '' (T.triangle i).carrier := by
  ext z
  constructor
  · rintro ⟨p, member, rfl⟩
    rw [T.cover] at member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    apply Set.mem_iUnion.mpr
    refine ⟨i, (K.projectFaceEquiv (T.face i)).symm p, ?_, ?_⟩
    · rw [T.triangle_carrier]
      exact ⟨p, member, rfl⟩
    · exact (K.roofPoint_eq_support_placement (T.face i) (T.active i p member)).symm
  · intro covered
    obtain ⟨i, x, member, rfl⟩ := Set.mem_iUnion.mp covered
    rw [T.triangle_carrier] at member
    obtain ⟨p, member, rfl⟩ := member
    refine ⟨p, ?_, (K.roofPoint_eq_support_placement (T.face i) (T.active i p member))⟩
    rw [T.cover]
    exact Set.mem_iUnion.mpr ⟨i, member⟩

/-- Each new physical triangle has the same actual unit normal as its supporting original face. -/
theorem normal_unit (i : T.Index) : ‖T.normal i‖ = 1 := K.normal_unit _

theorem normal_upward (i : T.Index) : 0 < T.normal i 2 := K.normal_upward _

theorem normal_tangent (i : T.Index) (x : Plane) :
    inner ℝ (T.normal i) ((T.placement i).linear x) = 0 := K.normal_tangent _ _

theorem tilt_preserved {φ : ℝ} (tilt : K.TiltBound φ) (i : T.Index) :
    Real.cos φ ≤ T.normal i 2 := tilt _

end ClipSpatialTriangles
end Unfoldings.ConvexCap
