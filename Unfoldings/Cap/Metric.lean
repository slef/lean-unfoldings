module

public import Unfoldings.Cap.ProjectedFaces
public import Unfoldings.Cap.Topology
public import Unfoldings.Metric.ConvexCover

/-!
# Uniform intrinsic projection bounds for convex caps

Local face bounds pass across the finite projected triangle cover. Thus the
inverse projection controls the actual route metric, not merely spatial chords,
with a constant depending only on normal height and not on the mesh size.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

include K

theorem connectedSpace : ConnectedSpace (C.Realization Set.univ) := by
  let : ContractibleSpace K.footprint := K.convex_projection.contractibleSpace
    (K.interior_projection.mono interior_subset)
  exact K.footprintHomeomorph.symm.surjective.connectedSpace
    K.footprintHomeomorph.symm.continuous

theorem edist_ne_top (x y : C.Realization Set.univ) : edist x y ≠ ⊤ := by
  let := K.connectedSpace
  exact edist_ne_top_of_preconnected x y

/-- The ordinary intrinsic metric, with the original route edistance and topology. -/
@[instance_reducible] def metricSpace : MetricSpace (C.Realization Set.univ) :=
  EMetricSpace.toMetricSpace K.edist_ne_top

/-- Projection cannot increase the actual intrinsic distance. -/
theorem projection_lipschitz : LipschitzWith 1 K.toFootprint := by
  have horizontal : LipschitzWith 1 Cap.horizontal := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
      Cap.horizontal_norm_le (x - y)
  have composition := horizontal.comp (K.folding.toSpace_lipschitz Set.univ)
  intro x y
  simpa only [mul_one, toFootprint, Subtype.edist_eq, Function.comp_apply] using
    composition.edist_le_mul x y

/-- Face contraction bounds extend across the whole convex footprint in the intrinsic metric. -/
theorem inverse_projection_lipschitz {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) :
    LipschitzWith ⟨c⁻¹, inv_nonneg.mpr positive.le⟩ K.footprintHomeomorph.symm := by
  let := K.metricSpace
  let pieces : Face → Set K.footprint :=
    fun f => Subtype.val ⁻¹' (K.projectedTriangle f).carrier
  have closed (f : Face) : IsClosed (pieces f) :=
    (K.projectedTriangle f).compact_carrier.isClosed.preimage continuous_subtype_val
  have cover : ⋃ f, pieces f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨f, present⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset p.property)
    exact Set.mem_iUnion.mpr ⟨f, present⟩
  have bounded (f : Face) :
      LipschitzOnWith ⟨c⁻¹, inv_nonneg.mpr positive.le⟩ K.footprintHomeomorph.symm (pieces f) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    change p.val ∈ (K.projectedTriangle f).carrier at hp
    change q.val ∈ (K.projectedTriangle f).carrier at hq
    rw [projectedTriangle, Triangle.affineImage_carrier] at hp hq
    obtain ⟨x, hx, px⟩ := hp
    obtain ⟨y, hy, qy⟩ := hq
    let a : C.Cell f := ⟨x, hx⟩
    let b : C.Cell f := ⟨y, hy⟩
    have first : K.footprintHomeomorph.symm p = C.faceMap Set.univ f a := by
      apply K.footprintHomeomorph.injective
      exact (K.footprintHomeomorph.apply_symm_apply p).trans (Subtype.ext px.symm)
    have last : K.footprintHomeomorph.symm q = C.faceMap Set.univ f b := by
      apply K.footprintHomeomorph.injective
      exact (K.footprintHomeomorph.apply_symm_apply q).trans (Subtype.ext qy.symm)
    rw [first, last, (K.folding.faceMap_isometry Set.univ f).dist_eq]
    change dist x y ≤ c⁻¹ * dist p.val q.val
    have lower : c * dist x y ≤ dist p.val q.val := by
      calc
        c * dist x y ≤ K.normal f 2 * dist x y :=
          mul_le_mul_of_nonneg_right (height f) dist_nonneg
        _ ≤ dist (K.projectFace f x) (K.projectFace f y) := K.face_projection_lower f x y
        _ = dist p.val q.val := by rw [px, qy]
    have result : dist x y ≤ dist p.val q.val / c := (le_div_iff₀ positive).mpr (by
      simpa only [mul_comm] using lower)
    simpa only [div_eq_mul_inv, mul_comm] using result
  exact convex_subtype_lipschitzWith_of_finite_closed_cover K.footprint K.convex_projection
    pieces closed cover K.footprintHomeomorph.symm _ bounded

/-- Quantitative inverse projection, with the route metric retained in the conclusion. -/
theorem projection_antilipschitz {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) :
    AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr positive.le⟩ K.toFootprint := by
  intro x y
  have estimate := (K.inverse_projection_lipschitz positive height).edist_le_mul
    (K.toFootprint x) (K.toFootprint y)
  simpa only [show K.toFootprint = K.footprintHomeomorph from rfl,
    Homeomorph.symm_apply_apply] using estimate

end Unfoldings.ConvexCap
