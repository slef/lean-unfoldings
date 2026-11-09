module

public import Unfoldings.Cone.SurfaceComparison
public import Unfoldings.Cone.TangentComparison

/-!
# Exact local cone metrics

Combining the two route comparisons gives exact pairwise distances on a
whole tangent neighborhood, together with coverage of every original face
that can occur in the corresponding intrinsic vertex ball.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- Quantitative local cone geometry, with all fields constructed below. -/
structure TangentNeighborhood where
  radius : ℝ
  positive : 0 < radius
  inside : ∀ a : C.TangentTotal retain v,
    edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) < ENNReal.ofReal radius →
      a.2.val ∈ (C.triangle a.1.val.1).carrier
  incident : ∀ a : C.Total,
    edist (C.vertexPoint retain v) (MetricGluing.point C.Cell (C.glue retain) a) <
      ENNReal.ofReal radius → ∃ c : C.CornerAt retain v, c.val.1 = a.1
  exact_distance : ∀ a b : C.TangentTotal retain v,
    edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) < ENNReal.ofReal radius →
    edist (C.tangentOrigin retain v) (C.tangentPoint retain v b) < ENNReal.ofReal radius →
    edist (C.tangentSurfaceTag retain v a) (C.tangentSurfaceTag retain v b) =
      edist (C.tangentPoint retain v a) (C.tangentPoint retain v b)

/-- Any point in an incident original triangle has its actual coordinate lift to the fan. -/
theorem exists_tangentSurfaceTag_lift (a : C.Total)
    (incident : ∃ c : C.CornerAt retain v, c.val.1 = a.1) :
    ∃ b : C.TangentTotal retain v,
      b.2.val ∈ (C.triangle b.1.val.1).carrier ∧
      C.tangentSurfaceTag retain v b = MetricGluing.point C.Cell (C.glue retain) a := by
  obtain ⟨f, x⟩ := a
  obtain ⟨⟨⟨g, i⟩, vertex⟩, faces⟩ := incident
  change g = f at faces
  subst g
  let c : C.CornerAt retain v := ⟨(f, i), vertex⟩
  exact ⟨⟨c, C.tangentInclude retain v c x⟩, x.property,
    C.tangentSurfaceTag_of_mem retain v _ x.property⟩

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem exists_tangentNeighborhood : Nonempty (C.TangentNeighborhood retain v) := by
  obtain ⟨δ, δpos, inside, lower⟩ := F.exists_tangentSurfaceTag_edist_le retain v
  obtain ⟨ε, εpos, upper⟩ := F.exists_surfaceTangentCell_edist_le retain v
  obtain ⟨η, ηpos, incident⟩ := C.exists_radius_cornerAt_face retain v
  let r := min δ (min ε η)
  have positive : 0 < r := lt_min δpos (lt_min εpos ηpos)
  have cone_small : r ≤ δ := min_le_left _ _
  have surface_small : r ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have incident_small : r ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  have contained (a : C.TangentTotal retain v)
      (near : edist (C.tangentOrigin retain v) (C.tangentPoint retain v a) <
        ENNReal.ofReal r) : a.2.val ∈ (C.triangle a.1.val.1).carrier :=
    inside a (near.trans_le (ENNReal.ofReal_le_ofReal cone_small))
  refine ⟨⟨r, positive, contained, ?_, ?_⟩⟩
  · intro a ha
    exact incident a (ha.trans_le (ENNReal.ofReal_le_ofReal incident_small))
  · intro a b ha hb
    apply le_antisymm
    · exact lower a b (ha.trans_le (ENNReal.ofReal_le_ofReal cone_small))
        (hb.trans_le (ENNReal.ofReal_le_ofReal cone_small))
    · let a' : C.Total := ⟨a.1.val.1, ⟨a.2.val, contained a ha⟩⟩
      let b' : C.Total := ⟨b.1.val.1, ⟨b.2.val, contained b hb⟩⟩
      have original_a : MetricGluing.point C.Cell (C.glue retain) a' =
          C.tangentSurfaceTag retain v a :=
        (C.tangentSurfaceTag_of_mem retain v a (contained a ha)).symm
      have original_b : MetricGluing.point C.Cell (C.glue retain) b' =
          C.tangentSurfaceTag retain v b :=
        (C.tangentSurfaceTag_of_mem retain v b (contained b hb)).symm
      have near_a : edist (C.vertexPoint retain v)
          (MetricGluing.point C.Cell (C.glue retain) a') < ENNReal.ofReal ε := by
        rw [original_a, F.tangentSurfaceTag_radial retain v a (contained a ha)]
        exact ha.trans_le (ENNReal.ofReal_le_ofReal surface_small)
      have near_b : edist (C.vertexPoint retain v)
          (MetricGluing.point C.Cell (C.glue retain) b') < ENNReal.ofReal ε := by
        rw [original_b, F.tangentSurfaceTag_radial retain v b (contained b hb)]
        exact hb.trans_le (ENNReal.ofReal_le_ofReal surface_small)
      have bound := upper a' b' near_a near_b
      rw [original_a, original_b] at bound
      have back_a : C.surfaceTangentCell retain v a'.1 a'.2 = C.tangentPoint retain v a :=
        F.surfaceTangentCell_surfaceTag retain v a (contained a ha)
      have back_b : C.surfaceTangentCell retain v b'.1 b'.2 = C.tangentPoint retain v b :=
        F.surfaceTangentCell_surfaceTag retain v b (contained b hb)
      rwa [back_a, back_b] at bound

end Unfoldings.SpatialFolding
