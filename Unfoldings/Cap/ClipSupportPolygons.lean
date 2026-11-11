module

public import Unfoldings.Cap.ClipDisk
public import Unfoldings.Geometry.CompactHalfplanes
public import Unfoldings.Geometry.ConvexPolygonPartition

/-!
# Actual compact polygons in each original supporting plane

Intersect an active support cell with a lower horizontal roof clip. The
intersection is compact, convex, and has interior, since it contains the
original projected triangle. Its exact finite rim and genuine nonoverlapping
triangle partition are constructed from its actual affine inequalities.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def clippedSupportCell (Z : ℝ) (f : Face) : Set Plane := K.clipFootprint Z ∩ K.roofCell f

theorem convex_clippedSupportCell (Z : ℝ) (f : Face) : Convex ℝ (K.clippedSupportCell Z f) :=
  (K.convex_clipFootprint Z).inter (K.convex_roofCell f)

theorem isCompact_clippedSupportCell {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) (f : Face) :
    IsCompact (K.clippedSupportCell Z f) :=
  (K.isCompact_clipFootprint member positive lower).inter_right (K.isClosed_roofCell f)

theorem projectedTriangle_subset_clippedSupportCell {Z : ℝ} (lower : Z ≤ 0) (f : Face) :
    (K.projectedTriangle f).carrier ⊆ K.clippedSupportCell Z f := by
  intro p in_triangle
  have footprint : p ∈ K.footprint := by
    rw [K.footprint_eq_union_projectedTriangles]
    exact Set.mem_iUnion.mpr ⟨f, in_triangle⟩
  have on_plane : p ∈ K.roofCell f := by
    rw [projectedTriangle, Triangle.affineImage_carrier] at in_triangle
    obtain ⟨x, carrier, rfl⟩ := in_triangle
    exact K.projectFace_mem_roofCell f ⟨x, carrier⟩
  exact ⟨K.footprint_subset_clip Z lower footprint, on_plane⟩

theorem clippedSupportCell_interior_nonempty {Z : ℝ} (lower : Z ≤ 0) (f : Face) :
    (interior (K.clippedSupportCell Z f)).Nonempty :=
  (K.projectedTriangle f).interior_nonempty.mono
    (interior_mono (K.projectedTriangle_subset_clippedSupportCell lower f))

/-- The zero differences between duplicate original supporting planes are explicitly omitted. -/
def clipSupportEquation (Z : ℝ) (f : Face) :
    Unit ⊕ {g : Face // K.supportHeight f ≠ K.supportHeight g} → Plane →ᵃ[ℝ] ℝ :=
  Sum.elim (fun _ => AffineMap.const ℝ Plane Z - K.supportHeight f)
    (fun g => K.supportHeight f - K.supportHeight g.val)

theorem clipSupportEquation_ne_zero {q : Plane} (_member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) (f : Face)
    (i : Unit ⊕ {g : Face // K.supportHeight f ≠ K.supportHeight g}) :
    K.clipSupportEquation Z f i ≠ 0 := by
  cases i with
  | inl token =>
    intro zero
    have at_q := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A q) zero
    change Z - K.supportHeight f q = 0 at at_q
    linarith [K.roofHeight_le_supportHeight q f]
  | inr g => exact fun zero => g.property (sub_eq_zero.mp zero)

theorem clippedSupportCell_eq_nonpositiveRegion (Z : ℝ) (f : Face) :
    K.clippedSupportCell Z f = nonpositiveRegion (K.clipSupportEquation Z f) := by
  classical
  ext p
  constructor
  · rintro ⟨clip, cell⟩ i
    cases i with
    | inl token =>
      change Z - K.supportHeight f p ≤ 0
      exact sub_nonpos.mpr (clip.trans (K.roofHeight_le_supportHeight p f))
    | inr g =>
      change K.supportHeight f p - K.supportHeight g.val p ≤ 0
      exact sub_nonpos.mpr (cell g.val)
  · intro inequalities
    have level : Z ≤ K.supportHeight f p := sub_nonpos.mp (inequalities (Sum.inl ()))
    have cell : p ∈ K.roofCell f := by
      intro g
      by_cases same : K.supportHeight f = K.supportHeight g
      · exact (congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A p) same).le
      · exact sub_nonpos.mp (inequalities (Sum.inr ⟨g, same⟩))
    have realizes := (K.mem_roofCell_iff f p).mp cell
    refine ⟨?_, cell⟩
    change Z ≤ K.roofHeight p
    rwa [realizes]

theorem exists_finite_clippedSupportCell_boundary_segments {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) (f : Face) :
    ∃ edges : Set (Plane × Plane), edges.Finite ∧
      frontier (K.clippedSupportCell Z f) = segmentCarrier edges := by
  have compact := K.isCompact_clippedSupportCell member positive lower f
  rw [K.clippedSupportCell_eq_nonpositiveRegion] at compact ⊢
  exact exists_finite_nonpositive_boundary_segments (K.clipSupportEquation Z f)
    (K.clipSupportEquation_ne_zero member positive lower f) compact

/-- Each original active support polygon has a constructed genuine finite triangle partition. -/
theorem exists_clippedSupportCell_triangle_partition {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) (f : Face) :
    ∃ (I : Type) (_ : Finite I) (triangle : I → Triangle),
      K.clippedSupportCell Z f = ⋃ i, (triangle i).carrier ∧
      Pairwise (fun i j =>
        Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)) := by
  obtain ⟨edges, finite, boundary⟩ :=
    K.exists_finite_clippedSupportCell_boundary_segments member positive lower f
  exact exists_finite_triangle_partition_of_convex_polygon
    (K.isCompact_clippedSupportCell member positive lower f) (K.convex_clippedSupportCell Z f)
    (K.clippedSupportCell_interior_nonempty lower f) edges finite boundary

end Unfoldings.ConvexCap
