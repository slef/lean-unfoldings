module

public import Unfoldings.Complex.Exact
public import Unfoldings.Metric.IsometricCells
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Spatial foldings of a triangle complex

Rigid face placements into three-dimensional space agree across every original
seam. They induce nonexpanding maps from every cut realization, and prove that
each original triangle retains its Euclidean metric. Global embedding and
convexity are separate properties, not implicit in a folding.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

universe u v

variable {Face : Type u} [Fintype Face]

/-- Spatial isometric face placements, compatible with all original seams. -/
structure SpatialFolding (C : TriangleComplex.{u, v} Face) where
  place : Face → Plane →ᵃⁱ[ℝ] Space
  joined : ∀ s, ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    place (C.left s).face x.val = place (C.right s).face (C.identify s x).val

namespace SpatialFolding

variable {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F in
/-- A rigid spatial folding rules out pairing two distinct edges of the same triangle. -/
theorem incident_faces_ne (s : C.Seam) : (C.left s).face ≠ (C.right s).face := by
  intro same
  obtain ⟨x, regular⟩ := (C.triangle (C.left s).face).exists_edge_nonvertex (C.left s).edge
  have joined := F.joined s x
  rw [congrArg F.place same] at joined
  have coordinates : x.val = (C.identify s x).val := (F.place (C.right s).face).injective joined
  have right : C.OnEdge (C.right s) (C.edgePoint (C.left s) x) := by
    refine ⟨same, ?_⟩
    change x.val ∈ (C.triangle (C.right s).face).edge (C.right s).edge
    rw [coordinates]
    exact (C.identify s x).property
  have regular' : ¬ C.IsVertex (C.edgePoint (C.left s) x) := regular
  exact C.distinct s (C.onEdge_unique regular' (C.edgePoint_onEdge (C.left s) x) right)

theorem face_isometry (f : Face) : Isometry (fun x : C.Cell f => F.place f x.val) :=
  (F.place f).isometry.comp isometry_subtype_coe

theorem compatible (retain : Set C.Seam) : ∀ a b, C.glue retain a b →
    F.place a.1 a.2.val = F.place b.1 b.2.val := by
  rintro a b ⟨s, hs, x, rfl, rfl⟩
  exact F.joined s x

/-- The spatial folding of a cut realization, without assuming global injectivity. -/
def toSpace (retain : Set C.Seam) : C.Realization retain → Space :=
  MetricGluing.lift C.Cell (C.glue retain) (fun f x => F.place f x.val)
    (fun f => (F.face_isometry f).lipschitzWith) (F.compatible retain)

@[simp] theorem toSpace_faceMap (retain : Set C.Seam) (f : Face) (x : C.Cell f) :
    F.toSpace retain (C.faceMap retain f x) = F.place f x.val := rfl

theorem toSpace_lipschitz (retain : Set C.Seam) : LipschitzWith 1 (F.toSpace retain) :=
  MetricGluing.lift_lipschitz C.Cell (C.glue retain) (fun f x => F.place f x.val)
    (fun f => (F.face_isometry f).lipschitzWith) (F.compatible retain)

include F in
/-- Ambient chord lower bounds and intrinsic straight segments give exact within-face distances. -/
theorem faceMap_isometry (retain : Set C.Seam) (f : Face) : Isometry (C.faceMap retain f) :=
  MetricGluing.of_isometry_of_compatible C.Cell (C.glue retain)
    (fun f x => F.place f x.val) F.face_isometry (F.compatible retain) f

@[simp] theorem toSpace_forgetCuts {retain retain' : Set C.Seam} (inclusion : retain ⊆ retain')
    (x : C.Realization retain) :
    F.toSpace retain' (C.forgetCuts inclusion x) = F.toSpace retain x := by
  obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  change F.toSpace retain' (C.forgetCuts inclusion (C.faceMap retain f x)) =
    F.toSpace retain (C.faceMap retain f x)
  rw [C.forgetCuts_faceMap, F.toSpace_faceMap, F.toSpace_faceMap]

/-- The spatial image of one whole closed triangular face. -/
def faceImage (f : Face) : Set Space := F.place f '' (C.triangle f).carrier

/-- The spatial union of all original triangular faces. -/
def surface : Set Space := ⋃ f, F.faceImage f

theorem compact_faceImage (f : Face) : IsCompact (F.faceImage f) :=
  (C.triangle f).compact_carrier.image (F.place f).continuous

theorem compact_surface : IsCompact F.surface := isCompact_iUnion F.compact_faceImage

theorem range_toSpace (retain : Set C.Seam) : Set.range (F.toSpace retain) = F.surface := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
    exact Set.mem_iUnion.mpr ⟨f, x.val, x.property, rfl⟩
  · intro hz
    obtain ⟨f, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    exact ⟨C.faceMap retain f ⟨x, hx⟩, rfl⟩

/-- The uncut intrinsic surface embeds spatially; cuts can still have distinct coincident banks. -/
def IsEmbedded : Prop := Function.Injective (F.toSpace Set.univ)

theorem isEmbedded_iff : F.IsEmbedded ↔ ∀ a b : C.Total,
    F.place a.1 a.2.val = F.place b.1 b.2.val → Relation.EqvGen (C.glue Set.univ) a b := by
  constructor
  · intro embedded a b equal
    apply (C.point_eq_iff Set.univ a b).mp
    apply embedded
    exact equal
  · intro exact x y equal
    obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
    obtain ⟨b, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) y
    exact (C.point_eq_iff Set.univ a b).mpr (exact a b equal)

/-- The spatial map with codomain restricted to the actual union of triangles. -/
def toSurface (retain : Set C.Seam) : C.Realization retain → F.surface :=
  fun x => ⟨F.toSpace retain x, (F.range_toSpace retain).le ⟨x, rfl⟩⟩

theorem toSurface_continuous (retain : Set C.Seam) : Continuous (F.toSurface retain) :=
  (F.toSpace_lipschitz retain).continuous.subtype_mk _

theorem toSurface_surjective (retain : Set C.Seam) : Function.Surjective (F.toSurface retain) := by
  intro y
  obtain ⟨x, hx⟩ := (F.range_toSpace retain).ge y.property
  exact ⟨x, Subtype.ext hx⟩

/-- The intrinsic uncut topology is the spatial subspace topology of an embedded surface. -/
def surfaceHomeomorph (embedded : F.IsEmbedded) : C.Realization Set.univ ≃ₜ F.surface :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (F.toSurface Set.univ)
    ⟨fun _ _ h => embedded (congrArg Subtype.val h), F.toSurface_surjective Set.univ⟩)
    (F.toSurface_continuous Set.univ)

@[simp] theorem surfaceHomeomorph_apply (embedded : F.IsEmbedded)
    (x : C.Realization Set.univ) :
    (F.surfaceHomeomorph embedded x).val = F.toSpace Set.univ x := rfl

end SpatialFolding
end Unfoldings
