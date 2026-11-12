module

public import Unfoldings.Cap.ClipOriginalFaceMap
public import Unfoldings.Cap.ClipOriginalRegularCopies
public import Unfoldings.Cap.ProjectedSeamUnique
public import Unfoldings.Geometry.EdgePerfect
public import Unfoldings.Topology.PerfectProjection

/-! Whole original retained seams, including endpoints, agree in the actual fine realization. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalSeamMapIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem originalFaceMap_eq_across_seam (lower : Z < 0) (retain : Set C.Seam)
    (s : C.Seam) (kept : s ∈ retain)
    (p : (K.projectedTriangle (C.left s).face).Edge (C.left s).edge) :
    L.originalFaceMap lower retain (C.left s).face
        ⟨p.val, (K.projectedTriangle _).edge_subset _ p.property⟩ =
      L.originalFaceMap lower retain (C.right s).face
        ⟨p.val, (K.projectedTriangle _).edge_subset _
          ((K.projected_seam_edges_eq s).subset p.property)⟩ := by
  let E := (K.projectedTriangle (C.left s).face).Edge (C.left s).edge
  let first (x : E) := L.originalFaceMap lower retain (C.left s).face
    ⟨x.val, (K.projectedTriangle _).edge_subset _ x.property⟩
  let last (x : E) := L.originalFaceMap lower retain (C.right s).face
    ⟨x.val, (K.projectedTriangle _).edge_subset _
      ((K.projected_seam_edges_eq s).subset x.property)⟩
  have first_continuous : Continuous first :=
    (L.originalFaceMap_continuous lower retain _).comp (continuous_subtype_val.subtype_mk _)
  have last_continuous : Continuous last :=
    (L.originalFaceMap_continuous lower retain _).comp (continuous_subtype_val.subtype_mk _)
  let good : Set E := {x | first x = last x}
  have closed : IsClosed good := isClosed_eq first_continuous last_continuous
  let exceptions : Set Plane :=
    (⋃ i : L.partition.Index, Set.range (L.partition.projectedTriangle i).vertex) ∪
      (⋃ f : Face, Set.range (K.projectedTriangle f).vertex)
  have finite_exceptions : exceptions.Finite :=
    (Set.finite_iUnion fun _ => Set.finite_range _).union
      (Set.finite_iUnion fun _ => Set.finite_range _)
  let bad : Set E := {x | x.val ∈ exceptions}
  have finite_bad : bad.Finite := finite_exceptions.of_injOn (f := fun x : E => x.val)
    (fun _ member => member) Subtype.val_injective.injOn
  have cover : Set.range (fun x : E => x) ⊆ good ∪ bad := by
    rintro x ⟨x, rfl⟩
    by_cases exceptional : x.val ∈ exceptions
    · exact Or.inr exceptional
    · apply Or.inl
      have regular : ∀ f k, x.val ≠ (K.projectedTriangle f).vertex k := by
        intro f k equal
        exact exceptional (Or.inr (Set.mem_iUnion.mpr ⟨f, k, equal.symm⟩))
      have outside : x.val ∉ K.projectedCutSet retain := by
        intro on_cut
        obtain ⟨t, on_cut⟩ := Set.mem_iUnion.mp on_cut
        obtain ⟨cut, on_edge⟩ := Set.mem_iUnion.mp on_cut
        have same := K.projected_seam_unique_at_regular_point s t x.property on_edge regular
        exact cut (same ▸ kept)
      obtain ⟨i, first_parent, first_member⟩ := L.original_piece_cover lower
        (C.left s).face x.val ((K.projectedTriangle _).edge_subset _ x.property)
      obtain ⟨j, last_parent, last_member⟩ := L.original_piece_cover lower
        (C.right s).face x.val ((K.projectedTriangle _).edge_subset _
          ((K.projected_seam_edges_eq s).subset x.property))
      have fine_regular : ¬ (L.partition.projectedTriangle i.val).IsVertex x.val := by
        rintro ⟨k, equal⟩
        exact exceptional (Or.inl (Set.mem_iUnion.mpr ⟨i.val, k, equal⟩))
      change first x = last x
      calc
        first x = L.originalPointCopy retain i x.val first_member :=
          L.originalFaceMap_eq lower retain _ _ i first_parent first_member
        _ = L.originalPointCopy retain j x.val last_member :=
          L.originalPointCopy_eq_away_cuts_of_regular retain x.val first_member last_member
            fine_regular outside
        _ = last x := (L.originalFaceMap_eq lower retain (C.right s).face
          ⟨x.val, (K.projectedTriangle _).edge_subset _
            ((K.projected_seam_edges_eq s).subset x.property)⟩
          j last_parent last_member).symm
  let : PerfectSpace E := (K.projectedTriangle (C.left s).face).edgePerfectSpace (C.left s).edge
  have all := range_subset_closed_of_perfect (fun x : E => x) continuous_id
    closed finite_bad cover (fun _ _ _ equal => equal)
  exact all ⟨p, rfl⟩

end Unfoldings.ConvexCap.LineAlignedClip
