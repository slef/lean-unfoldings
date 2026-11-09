module

public import Unfoldings.Complex.Geodesics
public import Unfoldings.Topology.FiniteIntervalCover
public import Unfoldings.Path.Subpath
public import Unfoldings.Path.Partition

/-!
# Bounded finite face descriptions of actual geodesics

Every visited face occupies one closed interval. Sort those actual endpoints
to subdivide the path into at most twice the original face count plus one
pieces, each wholly in a named original face. Spatial rigidity also proves
the exact affine parametrization of every piece. No general-position or
nonvertex-crossing premise is needed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {a b : C.Realization Set.univ} (p : Path a b)

structure FaceRoute where
  steps : ℕ
  time : Fin (steps + 1) → unitInterval
  increasing : StrictMono time
  start : time 0 = 0
  finish : time (Fin.last steps) = 1
  face : Fin steps → Face
  inside : ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ),
    p t ∈ Set.range (C.faceMap Set.univ (face i))

theorem FaceRoute.sum_edist (R : C.FaceRoute p) (geodesic : p.IsGeodesic) :
    ∑ i : Fin R.steps, edist (p (R.time i.castSucc)) (p (R.time i.succ)) = edist a b := by
  rw [geodesic.sum_partition_edist R.time R.increasing.monotone,
    R.start, R.finish, Path.source, Path.target]

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

theorem exists_geodesic_faceRoute (embedded : F.IsEmbedded)
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic) :
    ∃ R : C.FaceRoute p, R.steps ≤ 2 * Fintype.card Face + 1 := by
  classical
  let Visited := {f : Face // (C.faceTimes p f).Nonempty}
  have intervals (f : Visited) := F.faceTimes_eq_Icc embedded geodesic f.val f.property
  choose lower upper ordered interval using intervals
  have cover (t : unitInterval) : ∃ f : Visited, lower f ≤ t ∧ t ≤ upper f := by
    obtain ⟨⟨f, x⟩, image⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) (p t)
    have member : t ∈ C.faceTimes p f := ⟨x, image⟩
    let k : Visited := ⟨f, ⟨t, member⟩⟩
    exact ⟨k, (interval k).le member⟩
  obtain ⟨n, bound, time, increasing, start, finish, piece, inside⟩ :=
    exists_finite_interval_subdivision lower upper cover
  let R : C.FaceRoute p :=
    { steps := n
      time := time
      increasing := increasing
      start := start
      finish := finish
      face := fun i => (piece i).val
      inside := fun i t ht => (interval (piece i)).ge (inside i ht) }
  refine ⟨R, bound.trans ?_⟩
  have card : Fintype.card Visited ≤ Fintype.card Face := Fintype.card_subtype_le _
  omega

theorem geodesic_faceRoute_piece_eq_lineMap
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    (R : C.FaceRoute p) (i : Fin R.steps) (t : unitInterval) :
    F.toSpace Set.univ (p (Path.intervalParam (R.time i.castSucc) (R.time i.succ) t)) =
      AffineMap.lineMap (F.toSpace Set.univ (p (R.time i.castSucc)))
        (F.toSpace Set.univ (p (R.time i.succ))) (t : ℝ) := by
  obtain ⟨x, hx⟩ := R.inside i (R.time i.castSucc)
    ⟨le_rfl, (R.increasing Fin.castSucc_lt_succ).le⟩
  obtain ⟨y, hy⟩ := R.inside i (R.time i.succ)
    ⟨(R.increasing Fin.castSucc_lt_succ).le, le_rfl⟩
  have saturated : edist (F.toSpace Set.univ (p (R.time i.castSucc)))
      (F.toSpace Set.univ (p (R.time i.succ))) =
        edist (p (R.time i.castSucc)) (p (R.time i.succ)) := by
    rw [← hx, ← hy, F.toSpace_faceMap, F.toSpace_faceMap]
    exact (F.face_isometry (R.face i) x y).trans
      ((F.faceMap_isometry Set.univ (R.face i)) x y).symm
  exact (geodesic.subpath (R.time i.castSucc) (R.time i.succ)).map_eq_lineMap
    (F.toSpace Set.univ) (F.toSpace_lipschitz Set.univ) saturated t

theorem geodesic_faceRoute_spatial_length
    {a b : C.Realization Set.univ} {p : Path a b} (geodesic : p.IsGeodesic)
    (R : C.FaceRoute p) :
    ∑ i : Fin R.steps, edist (F.toSpace Set.univ (p (R.time i.castSucc)))
      (F.toSpace Set.univ (p (R.time i.succ))) = edist a b := by
  rw [← TriangleComplex.FaceRoute.sum_edist C p R geodesic]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨x, hx⟩ := R.inside i (R.time i.castSucc)
    ⟨le_rfl, (R.increasing Fin.castSucc_lt_succ).le⟩
  obtain ⟨y, hy⟩ := R.inside i (R.time i.succ)
    ⟨(R.increasing Fin.castSucc_lt_succ).le, le_rfl⟩
  rw [← hx, ← hy, F.toSpace_faceMap, F.toSpace_faceMap]
  exact (F.face_isometry (R.face i) x y).trans
    ((F.faceMap_isometry Set.univ (R.face i)) x y).symm

end Unfoldings.SpatialFolding
