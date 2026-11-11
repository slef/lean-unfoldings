module

public import Unfoldings.Cap.SectionTransitions
public import Unfoldings.Cap.Topology
public import Unfoldings.Complex.DiskCuts

/-!
# A constructed nonvertex rim anchor and its unique initial face

A midpoint of an actual original rim bank belongs to exactly one original
face and is distinct from every original projected corner. Every segment from
that anchor into the convex footprint starts in the same original face.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open Filter
open scoped Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

structure RimAnchor (_K : ConvexCap C) where
  bank : C.BoundaryBank Set.univ
  parameter : unitInterval
  positive : 0 < parameter
  small : parameter < 1

variable (K : ConvexCap C)

/-- Original disk topology constructs an actual bank; its midpoint supplies an anchor. -/
def rimAnchor : K.RimAnchor :=
  Classical.choice (by
    have connected := K.folding.boundaryGraph_connected_of_disk Set.univ K.diskHomeomorph
    obtain ⟨v⟩ := connected.nonempty
    obtain ⟨bank, _w, _link⟩ := C.boundaryGraph_vertex_incident Set.univ v
    exact ⟨⟨bank, ⟨1 / 2, by constructor <;> norm_num⟩,
      by change (0 : ℝ) < 1 / 2; norm_num,
      by change (1 / 2 : ℝ) < 1; norm_num⟩⟩)

namespace RimAnchor

variable {K} (A : K.RimAnchor)

def edgePoint : (C.triangle A.bank.val.face).Edge A.bank.val.edge :=
  C.bankParameter Set.univ A.bank A.parameter

def point : Plane := K.projectFace A.bank.val.face A.edgePoint.val

theorem nonvertex : ¬ (C.triangle A.bank.val.face).IsVertex A.edgePoint.val :=
  C.bankParameter_nonvertex Set.univ A.bank A.parameter A.positive A.small

theorem point_mem_face : A.point ∈ (K.projectedTriangle A.bank.val.face).carrier := by
  rw [projectedTriangle, Triangle.affineImage_carrier]
  exact ⟨A.edgePoint.val, (C.triangle A.bank.val.face).edge_subset _ A.edgePoint.property, rfl⟩

theorem point_mem_footprint : A.point ∈ K.footprint :=
  K.footprint_eq_union_projectedTriangles.symm ▸ Set.mem_iUnion.mpr ⟨_, A.point_mem_face⟩

/-- A genuine original bank interior point has one original face, before any additional cuts. -/
theorem point_unique_face {g : Face} (inside : A.point ∈ (K.projectedTriangle g).carrier) :
    g = A.bank.val.face := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at inside
  obtain ⟨y, carrier, image⟩ := inside
  let tagged : C.Total := ⟨g, ⟨y, carrier⟩⟩
  have equal : C.bankMap Set.univ A.bank A.edgePoint = C.faceMap Set.univ g ⟨y, carrier⟩ :=
    K.projection_injective image.symm
  have tags := (C.bankMap_eq_iff Set.univ A.bank A.edgePoint A.nonvertex tagged).mp equal
  exact (congrArg Sigma.fst tags).symm

/-- In particular the anchor is distinct from every original projected vertex. -/
theorem point_ne_corner (g : Face) (i : Fin 3) : A.point ≠ (K.projectedTriangle g).vertex i := by
  intro equal
  have same := A.point_unique_face (by
    rw [equal]
    exact (K.projectedTriangle g).vertex_mem i)
  subst g
  apply A.nonvertex
  refine ⟨i, ?_⟩
  apply K.projectFace_injective A.bank.val.face
  exact equal.symm

/-- The finite original-face cover has no competing face sufficiently near this bank midpoint. -/
theorem exists_face_neighborhood : ∃ r > 0, ∀ z ∈ K.footprint, dist z A.point < r →
    z ∈ (K.projectedTriangle A.bank.val.face).carrier := by
  classical
  have each (g : Face) : ∀ᶠ z in 𝓝 A.point,
      z ∈ (K.projectedTriangle g).carrier → g = A.bank.val.face := by
    by_cases same : g = A.bank.val.face
    · exact Eventually.of_forall (fun _ _ => same)
    · have outside : A.point ∉ (K.projectedTriangle g).carrier :=
        fun member => same (A.point_unique_face member)
      have near : ∀ᶠ z in 𝓝 A.point, z ∉ (K.projectedTriangle g).carrier :=
        (K.projectedTriangle g).compact_carrier.isClosed.isOpen_compl.mem_nhds outside
      exact near.mono (fun _ missing member => (missing member).elim)
  have all_faces : ∀ᶠ z in 𝓝 A.point,
      ∀ g, z ∈ (K.projectedTriangle g).carrier → g = A.bank.val.face := eventually_all.mpr each
  obtain ⟨r, positive, near⟩ := Metric.eventually_nhds_iff.mp all_faces
  refine ⟨r, positive, fun z footprint close => ?_⟩
  obtain ⟨g, member⟩ := Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset footprint)
  have same := near close g member
  exact same ▸ member

/-- All actual projected sections from the anchor start inside its one fixed original face. -/
theorem exists_initial_face_interval {q : Plane} (last : q ∈ K.footprint) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc 0 ε,
      AffineMap.lineMap A.point q t ∈ (K.projectedTriangle A.bank.val.face).carrier := by
  obtain ⟨r, positive, inside⟩ := A.exists_face_neighborhood
  have continuous : ContinuousAt (fun t : ℝ => AffineMap.lineMap A.point q t) 0 :=
    AffineMap.lineMap_continuous.continuousAt
  obtain ⟨δ, δpos, close⟩ := Metric.continuousAt_iff.mp continuous r positive
  let ε : ℝ := min (δ / 2) (1 / 2)
  have εpos : 0 < ε := lt_min (by positivity) (by norm_num)
  have εsmall : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have εδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ε, ⟨εpos, εsmall⟩, fun t bounds => ?_⟩
  apply inside _ (K.convex_projection.lineMap_mem A.point_mem_footprint last
    ⟨bounds.1, bounds.2.trans εsmall.le⟩)
  have near : dist t 0 < δ := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg bounds.1] using
      bounds.2.trans_lt εδ
  simpa only [AffineMap.lineMap_apply_zero] using close near

end RimAnchor
end Unfoldings.ConvexCap
