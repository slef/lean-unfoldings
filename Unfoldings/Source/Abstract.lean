module

public import Unfoldings.Source.AbstractBridge

/-!
# A formal abstract of source unfolding

This file introduces triangulated convex polyhedral boundaries, intrinsic distance,
and polygonal source nets, and proves the source-unfolding theorem at every
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

def edgePoint (a : Face × Corner) (x : edge (M.vertex a.1) a.2) : M.Point :=
  ⟨a.1, ⟨x.val, (convex_convexHull ℝ (Set.range (M.vertex a.1))).segment_subset
    (subset_convexHull ℝ _ ⟨a.2, rfl⟩)
    (subset_convexHull ℝ _ ⟨next a.2, rfl⟩) x.property⟩⟩

def glue (p q : M.Point) : Prop :=
  ∃ s, ∃ x, p = M.edgePoint (M.first s) x ∧
    q = M.edgePoint (M.last s) (M.identify s x)

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

/-- A source net is an embedded planar closed disk, subdivided into finitely many
nonoverlapping polygons that fold rigidly into the original triangles. Its interior
is exactly the cut-locus complement and is locally isometric to the original surface.
The cut can cross faces; it is not required to follow original edges.

The source is at the planar origin. Every radial segment folds to a shortest path,
and every normalized shortest path has exactly one radial lift, including tied
paths to the same endpoint. The entire net boundary folds onto the cut locus. -/
structure SourceNet {Face Seam : Type} [Fintype Face] [Fintype Seam]
    (M : Mesh Face Seam) (source : M.Surface) where
  region : Set Plane
  zero_interior : (0 : Plane) ∈ interior region
  disk : Nonempty (region ≃ₜ Metric.closedBall (0 : Plane) 1)
  fold : region → M.Surface
  continuous_fold : Continuous fold
  surjective_fold : Function.Surjective fold
  radial : ∀ (z : region) (t : unitInterval), (t : ℝ) • z.val ∈ region
  source_image : fold ⟨0, interior_subset zero_interior⟩ = source
  pieces : ∃ n : ℕ, ∃ piece : Fin n → Set Plane,
    (∀ i, Polygon (piece i)) ∧
    Pairwise (fun i j => Disjoint (interior (piece i)) (interior (piece j))) ∧
    (⋃ i, piece i) = region ∧
    ∃ face : Fin n → Face, ∃ motion : Fin n → Plane ≃ᵃⁱ[ℝ] Plane,
      ∀ i (x : piece i), ∃ h : motion i x.val ∈ triangle (M.vertex (face i)),
        ∃ hz : x.val ∈ region, fold ⟨x.val, hz⟩ = M.point ⟨face i, motion i x.val, h⟩
  polygonal_boundary : ∃ n : ℕ, ∃ a b : Fin n → Plane,
    frontier region = ⋃ i, segment ℝ (a i) (b i)
  cut_complement : ∃ H : interior region ≃ₜ ↥((M.cutLocus source)ᶜ),
    ∀ z, (H z).val = fold ⟨z.val, interior_subset z.property⟩
  local_isometry : ∀ x : interior region,
    ∃ T : Set (interior region), IsOpen T ∧ x ∈ T ∧
      ∀ y z : T, M.distance
        (fold ⟨y.val.val, interior_subset y.val.property⟩)
        (fold ⟨z.val.val, interior_subset z.val.property⟩) = edist y.val.val z.val.val
  boundary_projection : fold '' {z : region | z.val ∈ frontier region} = M.cutLocus source
  source_distance : ∀ z : region, M.distance source (fold z) = ENNReal.ofReal ‖z.val‖
  radial_geodesic : ∀ (z : region) (s t : unitInterval),
    M.distance (fold ⟨(s : ℝ) • z.val, radial z s⟩)
      (fold ⟨(t : ℝ) • z.val, radial z t⟩) = ENNReal.ofReal ‖z.val‖ * edist s t
  all_shortest_paths : ∀ x (p : Path source x), M.Shortest p →
    ∃! z : region, ∀ t : unitInterval, fold ⟨(t : ℝ) • z.val, radial z t⟩ = p t

/-- **The source-unfolding theorem.** Every nonextreme point of a triangulated convex
polyhedron has a finite nonoverlapping polygonal source net. A tagged source merely
chooses a face representation of the physical point. Sources on creases and flat
subdivision vertices are included; no generic-position assumption is needed. -/
theorem source_unfolding {Face Seam : Type} [Fintype Face] [Fintype Seam]
    (M : Mesh Face Seam) (K : Polyhedron M) (source : M.Point)
    (nonextreme : K.place source.1 source.2.val ∉
      (convexHull ℝ (Set.range (fun p : Face × Corner =>
        K.place p.1 (M.vertex p.1 p.2)))).extremePoints ℝ) :
    Nonempty (SourceNet M (M.point source)) := by
  classical
  let C := Unfoldings.CapAbstractBridge.meshComplex M.vertex M.nondegenerate
    M.first M.last M.distinct M.identify M.unique
  let F : Unfoldings.SpatialFolding C := ⟨K.place, K.joined⟩
  let D : Unfoldings.SourceAbstractBridge.NetData (C := C) M.Surface M.distance
      (fun f x => M.point ⟨f, x⟩) (M.point source) :=
    Unfoldings.SourceAbstractBridge.geometric_source_net F M.glue rfl
      K.embedded K.interior_nonempty K.boundary source nonextreme
  exact ⟨
    { region := D.region
      zero_interior := D.zero_interior
      disk := D.disk
      fold := D.fold
      continuous_fold := D.continuous_fold
      surjective_fold := D.surjective_fold
      radial := D.radial
      source_image := D.source_image
      pieces := D.pieces
      polygonal_boundary := D.polygonal_boundary
      cut_complement := D.cut_complement
      local_isometry := D.local_isometry
      boundary_projection := D.boundary_projection
      source_distance := D.source_distance
      radial_geodesic := D.radial_geodesic
      all_shortest_paths := D.all_shortest_paths }⟩

end Unfoldings.SourceAbstract
