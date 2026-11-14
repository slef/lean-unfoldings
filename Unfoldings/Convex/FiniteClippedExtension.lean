module

public import Unfoldings.Convex.FiniteDualPlanes

/-! The clipped extension is an actual finite polyhedral graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FiniteDual

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
  (point : I → Plane) (level : I → ℝ) (domain : J → Plane →ᵃ[ℝ] ℝ)

/-- Compact polygon clipping constructs finitely many actual slopes whose affine functions
realize the entire extension. These slopes are constructed from dual arrangement triangles. -/
theorem exists_finite_clipped_extension {Z : ℝ}
    (compact : IsCompact (AffineEnvelope.clip domain Z)) {q : Plane}
    (higher : Z < AffineEnvelope.height domain q) :
    ∃ (vertices : Finset Plane) (nonempty : vertices.Nonempty),
      (∀ p ∈ vertices, p ∈ AffineEnvelope.clip domain Z) ∧
      ∀ x : Plane,
        (clipped point level (AffineEnvelope.clip domain Z) compact
          ⟨q, higher.le⟩).height x =
            vertices.sup' nonempty (fun p => inner ℝ x p - cost point level p) := by
  classical
  obtain ⟨A, finite, triangle, plane, cover, affine⟩ :=
    exists_cost_partition point level domain compact higher
  let := Fintype.ofFinite A
  let vertices := Finset.univ.image (fun ai : A × Fin 3 => (triangle ai.1).vertex ai.2)
  have vertex_mem (a : A) (i : Fin 3) : (triangle a).vertex i ∈ vertices :=
    Finset.mem_image.mpr ⟨(a, i), Finset.mem_univ _, rfl⟩
  have inside (a : A) {p : Plane} (hp : p ∈ (triangle a).carrier) :
      p ∈ AffineEnvelope.clip domain Z := by
    rw [cover]
    exact Set.mem_iUnion.mpr ⟨a, hp⟩
  obtain ⟨a, _ha⟩ := Set.mem_iUnion.mp
    (cover ▸ (show q ∈ AffineEnvelope.clip domain Z from higher.le))
  have nonempty : vertices.Nonempty := ⟨(triangle a).vertex 0, vertex_mem a 0⟩
  have contained : ∀ p ∈ vertices, p ∈ AffineEnvelope.clip domain Z := by
    intro p hp
    obtain ⟨ai, _, rfl⟩ := Finset.mem_image.mp hp
    exact inside ai.1 ((triangle ai.1).vertex_mem ai.2)
  refine ⟨vertices, nonempty, contained, ?_⟩
  intro x
  let E := clipped point level (AffineEnvelope.clip domain Z) compact ⟨q, higher.le⟩
  let M := vertices.sup' nonempty (fun p => inner ℝ x p - cost point level p)
  have bound (a : A) {p : Plane} (hp : p ∈ (triangle a).carrier) :
      inner ℝ x p - cost point level p ≤ M := by
    let L : Plane →ᵃ[ℝ] ℝ := (innerSL ℝ (x - point (plane a))).toLinearMap.toAffineMap +
      AffineMap.const ℝ Plane (level (plane a))
    have identity (p : Plane) (hp : p ∈ (triangle a).carrier) :
        L p = inner ℝ x p - cost point level p := by
      change inner ℝ (x - point (plane a)) p + level (plane a) = _
      rw [inner_sub_left, affine a p hp]
      ring
    have on_vertices : Set.range (triangle a).vertex ⊆ L ⁻¹' Set.Iic M := by
      rintro p ⟨i, rfl⟩
      change L ((triangle a).vertex i) ≤ M
      rw [identity _ ((triangle a).vertex_mem i)]
      exact Finset.le_sup' (fun p => inner ℝ x p - cost point level p) (vertex_mem a i)
    have all := convexHull_min on_vertices ((convex_Iic M).affine_preimage L) hp
    change L p ≤ M at all
    rw [identity p hp] at all
    exact all
  apply le_antisymm
  · apply E.height_le
    intro p hp
    change p ∈ AffineEnvelope.clip domain Z at hp
    rw [cover] at hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact bound a ha
  · apply Finset.sup'_le
    intro p hp
    exact E.affine_le x (contained p hp)

end Unfoldings.FiniteDual
