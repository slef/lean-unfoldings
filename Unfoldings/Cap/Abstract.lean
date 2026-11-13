module

public import Unfoldings.Cap.AbstractBridge

/-!
# A formal abstract of the nearly flat convex cap theorem

This file introduces finite triangulations, geometric convex caps, and simple
polygon edge unfoldings, and proves the cap theorem. To assess its mathematical
meaning, read only the definitions and theorem statements here. Lean checks the
proofs through `AbstractBridge.lean` and the rest of the library.

Coordinates, rigid motions, convex hulls, quotients, and topology are standard
Mathlib notions. Points on different faces are identified only along the named
retained edges; equality of their eventual planar images is a separate condition.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.CapAbstract

/-- The local face plane, ambient three-dimensional space, and three triangle corners. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Corner := Fin 3

def next : Corner → Corner
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- A triangular face is the convex hull of its three corners. Its edges are closed segments. -/
def triangle (vertex : Corner → Plane) : Set Plane := convexHull ℝ (Set.range vertex)

def edge (vertex : Corner → Plane) (i : Corner) : Set Plane :=
  segment ℝ (vertex i) (vertex (next i))

/-- A finite triangulation specifies its corner coordinates and full-edge isometric pairings.
The determinant excludes degenerate triangles. Each local edge occurs in at most one pairing. -/
structure Mesh (Face Seam : Type*) [Fintype Face] [Fintype Seam] where
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

variable {Face Seam : Type*} [Fintype Face] [Fintype Seam] (M : Mesh Face Seam)

/-- A face point remembers which closed triangle it belongs to. -/
abbrev Point := (f : Face) × triangle (M.vertex f)

def edgePoint (a : Face × Corner) (x : edge (M.vertex a.1) a.2) : M.Point :=
  ⟨a.1, ⟨x.val, (convex_convexHull ℝ (Set.range (M.vertex a.1))).segment_subset
    (subset_convexHull ℝ _ ⟨a.2, rfl⟩)
    (subset_convexHull ℝ _ ⟨next a.2, rfl⟩) x.property⟩⟩

/-- Retaining a set of seams glues precisely those named pairs of whole edges.
The quotient uses finite chains of these identifications, including their reversals. -/
def glue (retain : Set Seam) (p q : M.Point) : Prop :=
  ∃ s ∈ retain, ∃ x, p = M.edgePoint (M.first s) x ∧
    q = M.edgePoint (M.last s) (M.identify s x)

abbrev Surface (retain : Set Seam) := Quot (M.glue retain)

/-- An original boundary edge is a local edge occurring in no seam pairing. -/
def boundaryEdge (a : Face × Corner) : Prop := ¬ ∃ s, a = M.first s ∨ a = M.last s

/-- The acute margin is a common positive distance of every triangle angle below a right angle. -/
def AcuteMargin (α : ℝ) : Prop := ∀ f i,
  EuclideanGeometry.angle (M.vertex f (next i)) (M.vertex f i)
    (M.vertex f (next (next i))) ≤ Real.pi / 2 - α

end Mesh

/-- Horizontal projection forgets the third coordinate. -/
def horizontal (p : Space) : Plane := WithLp.toLp 2 (fun i => p i.castSucc)

/-- The footprint is the horizontal projection of the union of the spatial closed faces. -/
def footprint {Face Seam : Type*} [Fintype Face] [Fintype Seam] (M : Mesh Face Seam)
    (place : Face → Plane →ᵃⁱ[ℝ] Space) : Set Plane :=
  horizontal '' (⋃ f, place f '' triangle (M.vertex f))

/-- A convex cap is an embedded, upward-facing, supported triangular surface over a convex
planar domain, with horizontal boundary at height zero. Normals are outward unit normals.
Projection identifies exactly points connected by the original seam pairings. -/
structure Cap {Face Seam : Type*} [Fintype Face] [Fintype Seam] (M : Mesh Face Seam) where
  place : Face → Plane →ᵃⁱ[ℝ] Space
  normal : Face → Space
  joined : ∀ s x, place (M.first s).1 x.val = place (M.last s).1 (M.identify s x).val
  unit : ∀ f, ‖normal f‖ = 1
  upward : ∀ f, 0 < normal f 2
  tangent : ∀ f x, inner ℝ (normal f) ((place f).linear x) = 0
  supporting : ∀ f (p : M.Point), inner ℝ (normal f) (place p.1 p.2.val - place f 0) ≤ 0
  projection : ∀ p q : M.Point,
    horizontal (place p.1 p.2.val) = horizontal (place q.1 q.2.val) →
      Relation.EqvGen (M.glue Set.univ) p q
  convex : Convex ℝ (footprint M place)
  interior_nonempty : (interior (footprint M place)).Nonempty
  rim : ∀ a, M.boundaryEdge a → ∀ x : edge (M.vertex a.1) a.2, place a.1 x.val 2 = 0
  above : ∀ f i, 0 ≤ place f (M.vertex f i) 2

/-- A simple polygon is a finite union of closed straight segments traversed by a continuous
loop that repeats no point before returning to its start. Collinear subdivisions are allowed. -/
def SimplePolygon (boundary : Set Plane) : Prop :=
  (∃ n : ℕ, ∃ a b : Fin n → Plane, boundary = ⋃ i, segment ℝ (a i) (b i)) ∧
    ∃ loop : ℝ → Plane, ContinuousOn loop (Set.Icc 0 1) ∧ loop 0 = loop 1 ∧
      Set.InjOn loop (Set.Ico 0 1) ∧ loop '' Set.Icc 0 1 = boundary

/-- An edge unfolding retains some original seams and places every face by a rigid planar
motion. Its cut surface is a disk. Planar equality is exactly retained-seam identification,
so the entire cut disk embeds, and its footprint frontier is a simple polygon. -/
def HasSimpleEdgeUnfolding {Face Seam : Type*} [Fintype Face] [Fintype Seam]
    (M : Mesh Face Seam) : Prop :=
  ∃ retain : Set Seam, Nonempty (M.Surface retain ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
    ∃ place : Face → Plane ≃ᵃⁱ[ℝ] Plane,
      (∀ p q : M.Point, place p.1 p.2.val = place q.1 q.2.val ↔
        Relation.EqvGen (M.glue retain) p q) ∧
      SimplePolygon (frontier (⋃ f, place f '' triangle (M.vertex f)))

/-- **The cap theorem.** For each positive acute margin there is a positive tilt bound,
chosen before the mesh. Every cap whose face normals satisfy that bound unfolds along
original edges into a simple polygon. No algorithmic time bound is asserted. -/
theorem nearly_flat_cap {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ {Face Seam : Type} [Fintype Face] [Fintype Seam] (M : Mesh Face Seam) (K : Cap M),
        M.AcuteMargin α → (∀ f, Real.cos φ ≤ K.normal f 2) → HasSimpleEdgeUnfolding M := by
  classical
  obtain ⟨φ, bounds, unfolds⟩ := Unfoldings.ConvexCap.orourke_cap_theorem.{0, 0} positive
  refine ⟨φ, bounds, ?_⟩
  intro Face Seam _ _ M K acute tilt
  let C := Unfoldings.CapAbstractBridge.meshComplex M.vertex M.nondegenerate
    M.first M.last M.distinct M.identify M.unique
  let F : Unfoldings.SpatialFolding C := ⟨K.place, K.joined⟩
  let cap := Unfoldings.CapAbstractBridge.capOfGeometricData F K.normal
    K.unit K.upward K.tangent K.supporting K.projection K.convex K.interior_nonempty
    (fun bank x => K.rim (bank.val.face, bank.val.edge)
      ((Unfoldings.CapAbstractBridge.boundary_edge_pair bank.val).mp bank.property) x) K.above
  obtain ⟨U⟩ := unfolds cap acute tilt
  exact Unfoldings.CapAbstractBridge.unfolding_output cap U

end Unfoldings.CapAbstract
