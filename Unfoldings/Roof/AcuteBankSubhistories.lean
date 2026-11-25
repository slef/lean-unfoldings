module

public import Unfoldings.Roof.AcutePhysicalBankRoll
public import Unfoldings.Complex.BoundaryChainIntervalRoll

/-! Uniform acute-cone bounds on every actual bank subhistory. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The acute-cone length and radial bounds apply simultaneously to every intrinsic subhistory. -/
theorem sharp_acute_physical_bank_subhistories
    {φ γ A : ℝ} (positive : 0 < φ) (small_phi : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    (gamma_positive : 0 < γ) (gamma_le : γ ≤ 1) (length_nonneg : 0 ≤ A)
    {retain : Set C.Seam} {n : ℕ} (bank : (C.boundarySystem retain).Chain n)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (bank.point i).val))
    (h k : Plane →L[ℝ] ℝ) (joint : Function.Bijective fun p => (h p, k p))
    (controls : let P := K.folding.projectedBoundaryChain bank
      (∀ i, 0 < h (P.edge i)) ∧ (∀ i, 0 < k (P.edge i)))
    (margin : let P := K.folding.projectedBoundaryChain bank
      ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
        γ * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
          inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))
    (lengths : let P := K.folding.projectedBoundaryChain bank
      ∀ (first length : ℕ) (fits : first + length ≤ n + 1),
        let interval := P.interval first length fits
        interval.projectedLength ≤ A * ‖interval.vertex (Fin.last length) - interval.vertex 0‖)
    (small : acuteConeDevelopmentError φ A < γ) :
    let E := acuteConeDevelopmentError φ A
    let D := (cos φ)⁻¹ * A / (1 - E)
    let d := (γ - E) / (1 + E)
    let Q := C.boundaryChainRoll bank
    (∀ (first length : ℕ) (fits : first + length ≤ n + 1),
      let interval := Q.interval first length fits
      interval.projectedLength ≤ D * ‖interval.vertex (Fin.last length) - interval.vertex 0‖) ∧
    ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      d * (‖Q.vertex i.castSucc - Q.vertex j‖ * ‖Q.edge i‖) ≤
        inner ℝ (Q.vertex i.castSucc - Q.vertex j) (Q.edge i) := by
  let P := K.folding.projectedBoundaryChain bank
  let Q := C.boundaryChainRoll bank
  let E := acuteConeDevelopmentError φ A
  let D := (cos φ)⁻¹ * A / (1 - E)
  let d := (γ - E) / (1 + E)
  have apply_to_slice (first length : ℕ) (fits : first + length ≤ n) :
      let seg := bank.interval first length fits
      let W := C.boundaryChainRoll seg
      K.BankRollAccuracy E D retain seg ∧
        d * (‖W.vertex (Fin.last length).castSucc - W.vertex 0‖ *
          ‖W.edge (Fin.last length)‖) ≤
          inner ℝ (W.vertex (Fin.last length).castSucc - W.vertex 0) (W.edge (Fin.last length)) := by
    let seg := bank.interval first length fits
    let S := K.folding.projectedBoundaryChain seg
    have same : S = P.interval first (length + 1) (by omega) :=
      K.folding.projectedBoundaryChain_interval bank first length fits
    have submargin (i : Fin (length + 1)) :
        γ * (‖S.vertex i.castSucc - S.vertex 0‖ * ‖S.edge i‖) ≤
          inner ℝ (S.vertex i.castSucc - S.vertex 0) (S.edge i) := by
      rw [same]
      exact margin ⟨first, by omega⟩ ⟨first + i.val, by omega⟩ (Nat.le_add_right _ _)
    have sublength (j : Fin (length + 2)) :
        (S.interval 0 j.val (PolygonalChain.initial_interval_fits j)).projectedLength ≤
          A * ‖S.vertex j - S.vertex 0‖ := by
      rw [same]
      have exact_slice :
          ((P.interval first (length + 1) (by omega)).interval 0 j.val
            (PolygonalChain.initial_interval_fits j)) =
          P.interval first j.val (by omega) := by
        cases P
        simp [PolygonalChain.interval]
      rw [exact_slice]
      exact lengths first j.val (by omega)
    have progress (f : Plane →L[ℝ] ℝ) (advance : ∀ i, 0 < f (P.edge i)) :
        ∀ i, 0 < f (S.edge i) := by
      intro i
      rw [same, PolygonalChain.interval_edge]
      exact advance _
    exact K.sharp_acute_physical_bank_roll positive small_phi height_bound tilt gamma_positive gamma_le
      length_nonneg seg (fun i => cut (bank.intervalIndex first length fits i)) h k joint
      ⟨progress h controls.1, progress k controls.2⟩ submargin sublength small
  constructor
  · intro first length fits
    cases length with
    | zero => simp [PolygonalChain.projectedLength]
    | succ m =>
      have fits' : first + m ≤ n := by omega
      have h := (apply_to_slice first m fits').1.length_bound
      rw [C.boundaryChainRoll_interval_projectedLength bank first m fits',
        C.boundaryChainRoll_interval_chord bank first m fits'] at h
      let T := complexRotation
        (-C.boundaryChainRollHeading bank (bank.intervalIndex first m fits' 0))
      let X := Q.interval first (m + 1) fits
      change X.projectedLength ≤ D * ‖T (X.vertex (Fin.last (m + 1)) - X.vertex 0)‖ at h
      rw [T.norm_map] at h
      exact h
  · intro j i earlier
    let length := i.val - j.val
    have fits : j.val + length ≤ n := by dsimp only [length]; omega
    let X := Q.interval j.val (length + 1) (by omega)
    let T := complexRotation
      (-C.boundaryChainRollHeading bank (bank.intervalIndex j.val length fits 0))
    have h := (apply_to_slice j.val length fits).2
    rw [C.boundaryChainRoll_interval_chord bank j.val length fits,
      C.boundaryChainRoll_interval_edge bank j.val length fits] at h
    have first : X.vertex 0 = Q.vertex j := rfl
    have last : X.vertex (Fin.last length).castSucc = Q.vertex i.castSucc :=
      congrArg Q.vertex (Fin.ext (by
        change j.val + length = i.val
        dsimp only [length]
        omega))
    have edge : X.edge (Fin.last length) = Q.edge i := by
      change (Q.interval j.val (length + 1) (by omega)).edge (Fin.last length) = Q.edge i
      rw [PolygonalChain.interval_edge]
      apply congrArg Q.edge
      apply Fin.ext
      change j.val + length = i.val
      dsimp only [length]
      omega
    change d * (‖T (X.vertex (Fin.last length).castSucc - X.vertex 0)‖ *
      ‖T (X.edge (Fin.last length))‖) ≤
      inner ℝ (T (X.vertex (Fin.last length).castSucc - X.vertex 0))
        (T (X.edge (Fin.last length))) at h
    simpa only [first, last, edge, T.norm_map, T.inner_map_map] using h

end Unfoldings.ConvexRoof
