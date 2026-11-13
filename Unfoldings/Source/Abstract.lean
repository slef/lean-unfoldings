module

public import Unfoldings.Source.AbstractBridge

/-!
# A formal abstract of source unfolding

This file introduces triangulated convex polyhedral boundaries, intrinsic distance,
and general net validity, and proves the source-unfolding theorem at every
nonextreme source. To assess the mathematical claim, read only these definitions
and theorem statements. Lean checks the proofs through `AbstractBridge.lean`
and the rest of the library. Genuine cone vertices are outside this theorem.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceAbstract

/-- Faces use a Euclidean plane; the polyhedron lies in Euclidean three-space.
Its three local corners and edges are indexed cyclically. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Corner := Fin 3

def next : Corner → Corner
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- A closed triangular face is the convex hull of its corners; its edges are segments. -/
def triangle (vertex : Corner → Plane) : Set Plane := convexHull ℝ (Set.range vertex)

def edge (vertex : Corner → Plane) (i : Corner) : Set Plane :=
  segment ℝ (vertex i) (vertex (next i))

/-- A finite triangulation consists of nondegenerate triangles and full-edge isometric
pairings, with each local edge used at most once. Subdivision vertices are allowed. -/
structure Mesh (Face Seam : Type) [Fintype Face] [Fintype Seam] where
  vertex : Face → Corner → Plane
  nondegenerate : ∀ f,
    (vertex f 1 0 - vertex f 0 0) * (vertex f 2 1 - vertex f 0 1) -
      (vertex f 1 1 - vertex f 0 1) * (vertex f 2 0 - vertex f 0 0) ≠ 0
  first : Seam → Face × Corner
  last : Seam → Face × Corner
  distinct : ∀ s, first s ≠ last s
  identify : ∀ s, edge (vertex (first s).1) (first s).2 ≃ᵢ
    edge (vertex (last s).1) (last s).2
  unique : ∀ s t, first s = first t ∨ first s = last t ∨
    last s = first t ∨ last s = last t → s = t

namespace Mesh

variable {Face Seam : Type} [Fintype Face] [Fintype Seam] (M : Mesh Face Seam)

/-- A tagged point lies in one closed triangle. The surface identifies points only by
finite chains of the prescribed edge pairings, including their reversals. -/
abbrev Point := (f : Face) × triangle (M.vertex f)

def glue (p q : M.Point) : Prop :=
  ∃ s, ∃ x : edge (M.vertex (M.first s).1) (M.first s).2,
    p.1 = (M.first s).1 ∧ p.2.val = x.val ∧
    q.1 = (M.last s).1 ∧ q.2.val = (M.identify s x).val

abbrev Surface := Quot M.glue

def point (p : M.Point) : M.Surface := Quot.mk M.glue p

/-- Intrinsic distance is the greatest extended pseudometric for which movement within
any face costs at most Euclidean distance. Equivalently, it is the infimum of lengths
of surface paths, rather than the length of the spatial chord. -/
def distance (x y : M.Surface) : ENNReal :=
  ⨆ d : M.Surface → M.Surface → ENNReal,
    ⨆ (_ : (∀ a, d a a = 0) ∧ (∀ a b, d a b = d b a) ∧
      (∀ a b c, d a c ≤ d a b + d b c) ∧
      (∀ f (a b : triangle (M.vertex f)),
        d (M.point ⟨f, a⟩) (M.point ⟨f, b⟩) ≤ edist a b)), d x y

/-- A shortest path is parameterized at constant speed on the unit interval.
Every pair of parameter values realizes the corresponding fraction of its endpoint distance. -/
def Shortest {a b : M.Surface} (p : Path a b) : Prop :=
  ∀ s t : unitInterval, M.distance (p s) (p t) = M.distance a b * edist s t

/-- The cut locus is the closure of points with two distinct normalized shortest paths.
Taking the closure retains leaves even when a leaf itself has only one incoming path. -/
def cutLocus (source : M.Surface) : Set M.Surface :=
  closure {x | ∃ p q : Path source x, M.Shortest p ∧ M.Shortest q ∧ p ≠ q}

end Mesh

/-- A convex polyhedron is a rigidly placed triangulation that embeds onto the boundary
of the full-dimensional convex hull of its spatial corners. Spatial coincidences must
come from the prescribed edge pairings; no metric or unfolding conclusion is assumed. -/
structure Polyhedron {Face Seam : Type} [Fintype Face] [Fintype Seam]
    (M : Mesh Face Seam) where
  place : Face → Plane →ᵃⁱ[ℝ] Space
  joined : ∀ s x, place (M.first s).1 x.val = place (M.last s).1 (M.identify s x).val
  embedded : ∀ p q : M.Point, place p.1 p.2.val = place q.1 q.2.val →
    Relation.EqvGen M.glue p q
  interior_nonempty :
    (interior (convexHull ℝ (Set.range (fun p : Face × Corner =>
      place p.1 (M.vertex p.1 p.2))))).Nonempty
  boundary : (⋃ f, place f '' triangle (M.vertex f)) =
    frontier (convexHull ℝ (Set.range (fun p : Face × Corner => place p.1 (M.vertex p.1 p.2))))

/-- A polygon is a compact intersection of finitely many closed affine halfplanes,
with nonempty interior. This excludes degenerate pieces. -/
def Polygon (s : Set Plane) : Prop :=
  IsCompact s ∧ (interior s).Nonempty ∧
    ∃ n : ℕ, ∃ halfplane : Fin n → Plane →ᵃ[ℝ] ℝ,
      s = {x | ∀ i, 0 ≤ halfplane i x}

/-- The spatial surface is the union of the placed closed triangles. -/
def Polyhedron.surface {Face Seam : Type} [Fintype Face] [Fintype Seam]
    {M : Mesh Face Seam} (K : Polyhedron M) : Set Space :=
  ⋃ f, K.place f '' triangle (M.vertex f)

/-- A net of a spatial surface is a planar closed disk with a continuous folding
onto that entire surface. Distinct interior points remain distinct on the surface.
The disk is a finite union of nonoverlapping polygons, and the folding on each
polygon is a rigid map into three-space. Its boundary consists of finitely many segments.
This definition applies to any spatial surface; it assumes no source or convexity. -/
def IsNetOf (surface : Set Space) (region : Set Plane) (fold : region → Space) : Prop :=
  Nonempty (region ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
  Continuous fold ∧ Set.range fold = surface ∧
  Set.InjOn fold {z : region | z.val ∈ interior region} ∧
  (∃ n : ℕ, ∃ piece : Fin n → Set Plane,
    (∀ i, Polygon (piece i)) ∧
    Pairwise (fun i j => Disjoint (interior (piece i)) (interior (piece j))) ∧
    (⋃ i, piece i) = region ∧
    ∃ motion : Fin n → Plane →ᵃⁱ[ℝ] Space,
      ∀ i (x : piece i), ∃ hz : x.val ∈ region, fold ⟨x.val, hz⟩ = motion i x.val) ∧
  ∃ n : ℕ, ∃ a b : Fin n → Plane, frontier region = ⋃ i, segment ℝ (a i) (b i)

/-- A source unfolding is a net of the given polyhedron with the source at the origin.
Its folding lifts to the abstract surface, identifies the interior with the cut-locus
complement by a local isometry, and maps the whole boundary exactly onto the cut locus.
Every radial segment folds to a shortest path, and every normalized shortest path
has exactly one radial lift, including distinct paths tied at one endpoint. -/
def IsSourceUnfolding {Face Seam : Type} [Fintype Face] [Fintype Seam]
    {M : Mesh Face Seam} (K : Polyhedron M) (source : M.Point)
    (region : Set Plane) (fold : region → Space) : Prop :=
  IsNetOf K.surface region fold ∧ ∃ project : region → M.Surface,
    Continuous project ∧ Function.Surjective project ∧
    (∀ z p, project z = M.point p → fold z = K.place p.1 p.2.val) ∧
    (0 : Plane) ∈ interior region ∧
    (∀ (z : region) (t : unitInterval), (t : ℝ) • z.val ∈ region) ∧
    (∀ h : (0 : Plane) ∈ region, project ⟨0, h⟩ = M.point source) ∧
    (∃ H : interior region ≃ₜ ↥((M.cutLocus (M.point source))ᶜ),
      ∀ z, (H z).val = project ⟨z.val, interior_subset z.property⟩) ∧
    (∀ x : interior region, ∃ T : Set (interior region), IsOpen T ∧ x ∈ T ∧
      ∀ y z : T, M.distance
        (project ⟨y.val.val, interior_subset y.val.property⟩)
        (project ⟨z.val.val, interior_subset z.val.property⟩) = edist y.val.val z.val.val) ∧
    project '' {z : region | z.val ∈ frontier region} = M.cutLocus (M.point source) ∧
    (∀ z : region, M.distance (M.point source) (project z) = ENNReal.ofReal ‖z.val‖) ∧
    (∀ (z : region) (s t : unitInterval)
      (hs : (s : ℝ) • z.val ∈ region) (ht : (t : ℝ) • z.val ∈ region),
      M.distance (project ⟨(s : ℝ) • z.val, hs⟩) (project ⟨(t : ℝ) • z.val, ht⟩) =
        ENNReal.ofReal ‖z.val‖ * edist s t) ∧
    ∀ x (p : Path (M.point source) x), M.Shortest p →
      ∃! z : region, ∀ t : unitInterval, ∃ hz : (t : ℝ) • z.val ∈ region,
        project ⟨(t : ℝ) • z.val, hz⟩ = p t

/-- **The source-unfolding theorem.** Every nonextreme point of a triangulated convex
polyhedron has a valid source unfolding of that polyhedron. A tagged source merely
chooses a face representation of the physical point. Sources on creases and flat
subdivision vertices are included; no generic-position assumption is needed. -/
theorem source_unfolding {Face Seam : Type} [Fintype Face] [Fintype Seam]
    (M : Mesh Face Seam) (K : Polyhedron M) (source : M.Point)
    (nonextreme : K.place source.1 source.2.val ∉
      (convexHull ℝ (Set.range (fun p : Face × Corner =>
        K.place p.1 (M.vertex p.1 p.2)))).extremePoints ℝ) :
    ∃ region : Set Plane, ∃ fold : region → Space, IsSourceUnfolding K source region fold := by
  exact Unfoldings.SourceAbstractBridge.abstract_source_unfolding M.vertex M.nondegenerate
    M.first M.last M.distinct M.identify M.unique K.place K.joined K.embedded
    K.interior_nonempty K.boundary source nonextreme

end Unfoldings.SourceAbstract
