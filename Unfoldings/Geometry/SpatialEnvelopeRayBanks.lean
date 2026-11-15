module

public import Unfoldings.Geometry.SpatialEnvelopeCutBanks
public import Unfoldings.Geometry.RayForwardHalfspace

/-! Whole positive rays produce two disjoint, exact metric bank tails in the physical cut space. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- Opposite copies over any positive point of an actual cut ray are metrically distinct. -/
theorem liftCell_ray_bank_ne (cuts : Set Plane) (p q : Plane) (different : p ≠ q)
    (cut_ray : ∀ t : ℝ, 0 ≤ t → AffineMap.lineMap p q t ∈ cuts)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a →
      0 ≤ AffineArrangement.signed (orientMap p q) (signs a) x)
    {a b : A} (x : P.footprint a) (y : P.footprint b)
    {t : ℝ} (positive : 0 < t) (position : x.val = AffineMap.lineMap p q t)
    (opposite : signs a ≠ signs b) : P.liftCell cuts a x ≠ P.liftCell cuts b y := by
  apply P.liftCell_ne_of_opposite_sign cuts (orientMap p q) signs aligned
    (isOpen_rayForwardHalfspace p q) ?_ x y ?_ opposite
  · intro z forward zero
    obtain ⟨s, hs, rfl⟩ := exists_positive_ray_parameter different forward zero
    exact cut_ray s hs.le
  · rw [position]
    exact lineMap_mem_rayForwardHalfspace different positive

/-- Construct two disjoint whole bank tails from an aligned partition and an actual cut ray.
Both folds are the original roof graph, and both preserve every spatial distance within the tail. -/
theorem exists_unbounded_ray_banks (cuts : Set Plane) (p q : Plane) (different : p ≠ q)
    (cut_ray : ∀ t : ℝ, 0 ≤ t → AffineMap.lineMap p q t ∈ cuts)
    (signs : A → Bool)
    (aligned : ∀ a x, x ∈ P.footprint a →
      0 ≤ AffineArrangement.signed (orientMap p q) (signs a) x) :
    ∃ T : ℝ, 0 < T ∧ ∃ L R : Set.Ici T → P.Cut cuts,
      (∀ t, (P.restoreCut cuts (L t)).val = point family (AffineMap.lineMap p q t.val) ∧
        (P.restoreCut cuts (R t)).val = point family (AffineMap.lineMap p q t.val)) ∧
      (∀ s t, edist (L s) (L t) =
        edist (point family (AffineMap.lineMap p q s.val))
          (point family (AffineMap.lineMap p q t.val))) ∧
      (∀ s t, edist (R s) (R t) =
        edist (point family (AffineMap.lineMap p q s.val))
          (point family (AffineMap.lineMap p q t.val))) ∧
      Disjoint (Set.range L) (Set.range R) := by
  have ray_eq (t : ℝ) : p + t • (q - p) = AffineMap.lineMap p q t := by
    rw [AffineMap.lineMap_apply_module', add_comm]
  obtain ⟨a, b, ha, hb, T, positive, tails⟩ := P.exists_opposite_ray_cells
    (orientMap p q) (orientMap_ne_zero different) signs aligned p (q - p)
    (fun t => by rw [ray_eq, orientMap_apply, orient_lineMap])
  have left (t : Set.Ici T) : AffineMap.lineMap p q t.val ∈ P.footprint a := by
    simpa only [ray_eq] using (tails t.val t.property).1
  have right (t : Set.Ici T) : AffineMap.lineMap p q t.val ∈ P.footprint b := by
    simpa only [ray_eq] using (tails t.val t.property).2
  let L : Set.Ici T → P.Cut cuts := fun t => P.liftCell cuts a ⟨_, left t⟩
  let R : Set.Ici T → P.Cut cuts := fun t => P.liftCell cuts b ⟨_, right t⟩
  refine ⟨T, positive, L, R, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨P.restoreCut_liftCell cuts a _, P.restoreCut_liftCell cuts b _⟩
  · intro s t
    exact P.edist_liftCell cuts a _ _
  · intro s t
    exact P.edist_liftCell cuts b _ _
  · rw [Set.disjoint_left]
    rintro z ⟨s, rfl⟩ ⟨t, equal⟩
    have separated := P.liftCell_ray_bank_ne cuts p q different cut_ray signs aligned
      ⟨_, left s⟩ ⟨_, right t⟩ (positive.trans_le s.property) rfl
      (by rw [ha, hb]; decide)
    exact separated equal.symm

end Unfoldings.SpatialEnvelope.WholePartition
