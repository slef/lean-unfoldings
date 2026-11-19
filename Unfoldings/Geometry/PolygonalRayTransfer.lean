module

public import Unfoldings.Geometry.PolygonalRayEmbedding
public import Unfoldings.Geometry.RadialChainTransfer

/-! Transport actual bank coordinates along the same closed edges and whole tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}

/-- Original closed-edge parameters and the true unbounded tail parameter. -/
abbrev Address (n : ℕ) := (Fin n × unitInterval) ⊕ ℝ≥0

/-- Addresses retain duplicate representatives at each finite edge endpoint and tail join. -/
def addressPoint (R : PolygonalRay E n) : Address n → E
  | .inl (i, t) => R.chain.point i t
  | .inr t => R.tail t

variable (R : PolygonalRay E n)

theorem addressPoint_mem (a : Address n) : R.addressPoint a ∈ R.carrier := by
  cases a with
  | inl p =>
    apply Or.inl
    rw [R.chain.path_range]
    exact Or.inr (Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩)
  | inr t => exact R.tail_mem t

/-- Every actual bank point has an original finite or infinite address, even with no bends. -/
theorem exists_address {x : E} (member : x ∈ R.carrier) :
    ∃ a : Address n, R.addressPoint a = x := by
  rcases member with finite_member | ⟨t, rfl⟩
  · rw [R.chain.path_range] at finite_member
    rcases finite_member with initial | finite
    · have same : x = R.start := Set.mem_singleton_iff.mp initial
      cases n with
      | zero => exact ⟨.inr 0, (R.tail_zero).trans same.symm⟩
      | succ n => exact ⟨.inl (0, 0), (R.chain.point_zero 0).trans same.symm⟩
    · obtain ⟨i, t, equal⟩ := Set.mem_iUnion.mp finite
      exact ⟨.inl (i, t), equal⟩
  · exact ⟨.inr t, rfl⟩

variable (outward : R.Outward) (genuine : ∀ i, R.chain.edge i ≠ 0)
  (nonzero : R.direction ≠ 0)

include outward genuine nonzero

/-- No bank address creates a false identification when transferred to another chain.
The target can bend arbitrarily and may overlap itself. -/
theorem transfer_address_eq (Q : PolygonalRay F n) (a b : Address n)
    (equal : R.addressPoint a = R.addressPoint b) :
    Q.addressPoint a = Q.addressPoint b := by
  have mixed (i : Fin n) (t : unitInterval) (s : ℝ≥0)
      (equal : R.chain.point i t = R.tail s) : Q.chain.point i t = Q.tail s := by
    have lower := (R.tail_radius_strictMono outward nonzero).monotone (show (0 : ℝ≥0) ≤ s from
      zero_le)
    have finite_member : R.chain.point i t ∈ Set.range R.chain.path := by
      rw [R.chain.path_range]
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, t, rfl⟩)
    have upper := R.prefix_radius_le outward finite_member
    have radius := congrArg (dist R.start) equal
    have at_zero : s = 0 := (R.tail_radius_strictMono outward nonzero).injective (by
      rw [R.tail_zero] at lower ⊢
      linarith)
    rw [at_zero, R.tail_zero] at equal
    obtain ⟨last, at_one⟩ := PolygonalChain.RadialFrom.point_eq_last R.chain outward.1 genuine
      i t equal
    rw [at_one, Q.chain.point_one, last, at_zero, Q.tail_zero]
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      exact PolygonalChain.RadialFrom.transfer_point_eq R.chain outward.1 genuine
        Q.chain p.1 q.1 p.2 q.2 equal
    | inr s => exact mixed p.1 p.2 s equal
  | inr t =>
    cases b with
    | inl q => exact (mixed q.1 q.2 t equal.symm).symm
    | inr s =>
      exact congrArg Q.tail ((R.tail_radius_strictMono outward nonzero).injective
        (congrArg (dist R.start) equal))

/-- A radial bank transports to its original physical bank by the actual edge and tail
parameters. Chosen representatives introduce no extra identifications. -/
def mapCarrier (Q : PolygonalRay F n) (x : R.carrier) : Q.carrier :=
  let a := (R.exists_address x.property).choose
  ⟨Q.addressPoint a, Q.addressPoint_mem a⟩

/-- Every original finite or infinite parameter is retained literally. -/
theorem mapCarrier_address (Q : PolygonalRay F n) (a : Address n) :
    R.mapCarrier Q ⟨R.addressPoint a, R.addressPoint_mem a⟩ =
      ⟨Q.addressPoint a, Q.addressPoint_mem a⟩ := by
  apply Subtype.ext
  exact R.transfer_address_eq outward genuine nonzero Q _ a
    (R.exists_address (R.addressPoint_mem a)).choose_spec

/-- The common source is preserved, including rays with no finite edges. -/
theorem mapCarrier_start (Q : PolygonalRay F n) :
    R.mapCarrier Q ⟨R.start, R.start_mem⟩ = ⟨Q.start, Q.start_mem⟩ := by
  cases n with
  | zero =>
    simpa only [addressPoint, tail_zero, start, Fin.last_zero] using
      R.mapCarrier_address outward genuine nonzero Q (.inr 0)
  | succ n =>
    simpa only [addressPoint, PolygonalChain.point_zero, start, Fin.castSucc_zero] using
      R.mapCarrier_address outward genuine nonzero Q (.inl (0, 0))

end Unfoldings.PolygonalRay
