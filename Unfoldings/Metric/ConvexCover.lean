module

public import Unfoldings.Geometry.ConvexCover
public import Mathlib.Analysis.Convex.Contractible
public import Unfoldings.Metric.Connected

/-!
# Finite convex-cover bounds with extended-metric targets

A refinement may have several components separated by infinite distance.
Nevertheless the image of each old convex cell is connected. Restricting to
that image gives an ordinary metric, so finite closed-piece bounds apply
without assuming the whole refined surface is connected.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

theorem convex_subtype_emetric_lipschitzWith_of_finite_closed_cover {E Y ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [EMetricSpace Y] [Finite ι]
    (s : Set E) (convex_s : Convex ℝ s) (pieces : ι → Set s)
    (closed : ∀ i, IsClosed (pieces i)) (cover : ⋃ i, pieces i = Set.univ)
    (f : s → Y) (K : ℝ≥0) (bounded : ∀ i, LipschitzOnWith K f (pieces i)) :
    LipschitzWith K f := by
  have continuous_f : Continuous f := by
    rw [continuous_iff_isClosed]
    intro t closed_t
    have equality : f ⁻¹' t = ⋃ i, pieces i ∩ f ⁻¹' t := by
      ext x
      constructor
      · intro member
        have present : x ∈ ⋃ i, pieces i := cover.symm ▸ Set.mem_univ x
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp present
        exact Set.mem_iUnion.mpr ⟨i, hi, member⟩
      · intro member
        obtain ⟨i, _hi, member⟩ := Set.mem_iUnion.mp member
        exact member
    rw [equality]
    exact isClosed_iUnion_of_finite (fun i =>
      (bounded i).continuousOn.preimage_isClosed_of_isClosed (closed i) closed_t)
  intro x y
  let : ContractibleSpace s := convex_s.contractibleSpace ⟨x.val, x.property⟩
  let g : s → Set.range f := fun z => ⟨f z, z, rfl⟩
  have continuous_g : Continuous g := continuous_f.subtype_mk (fun z => ⟨z, rfl⟩)
  have surjective_g : Function.Surjective g := by
    rintro ⟨z, w, rfl⟩
    exact ⟨w, rfl⟩
  let : ConnectedSpace (Set.range f) := surjective_g.connectedSpace continuous_g
  let : MetricSpace (Set.range f) := EMetricSpace.toMetricSpace
    (fun a b => edist_ne_top_of_preconnected a b)
  have piece_bound (i : ι) : LipschitzOnWith K g (pieces i) := by
    intro a ha b hb
    exact bounded i ha hb
  exact (convex_subtype_lipschitzWith_of_finite_closed_cover s convex_s pieces closed cover
    g K piece_bound).edist_le_mul x y

end Unfoldings
