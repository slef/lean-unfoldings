module

public import Unfoldings.Complex.PointSeamRoute
public import Unfoldings.Complex.Hinge

/-!
# Finite seam words and their constructed rigid placements

An oriented seam has a deterministic outward hinge motion, usable in either
direction. Finite words compose these motions. Bounded words form a finite
type, hence yield finitely many candidate rigid placements. Actual point
routes supply such words; no unfolding placement is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

abbrev BoundedSeamWord (N : ℕ) := (n : Fin N) × (Fin n.val → C.Seam × Bool)

def seamTransition (s : C.Seam) (side : Bool) : Plane ≃ᵃⁱ[ℝ] Plane :=
  if side then (C.seamHinge s).place.symm else (C.seamHinge s).place

theorem seamTransition_joined (s : C.Seam) (side : Bool)
    (x : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge) :
    C.seamTransition s side (C.across s side x).val = x.val := by
  cases side
  · exact (C.seamHinge s).joined x
  · change (C.seamHinge s).place.symm ((C.identify s).symm x).val = x.val
    apply (C.seamHinge s).place.injective
    rw [AffineIsometryEquiv.apply_symm_apply]
    have joined := (C.seamHinge s).joined ((C.identify s).symm x)
    have edge : C.identify s ((C.identify s).symm x) = x := (C.identify s).apply_symm_apply x
    rw [edge] at joined
    exact joined.symm

def wordPlacement : List (C.Seam × Bool) → (Plane ≃ᵃⁱ[ℝ] Plane) → (Plane ≃ᵃⁱ[ℝ] Plane)
  | [], initial => initial
  | letter :: rest, initial =>
    wordPlacement rest ((C.seamTransition letter.1 letter.2).trans initial)

theorem wordPlacement_on_chain {n : ℕ} (letters : Fin n → C.Seam × Bool)
    (points : Fin (n + 1) → Plane)
    (joined : ∀ i, C.seamTransition (letters i).1 (letters i).2 (points i.succ) =
      points i.castSucc) (initial : Plane ≃ᵃⁱ[ℝ] Plane) :
    C.wordPlacement (List.ofFn letters) initial (points (Fin.last n)) = initial (points 0) := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, wordPlacement]
    have tail_joined (i : Fin n) := joined i.succ
    have result := ih (fun i => letters i.succ) (fun i => points i.succ) tail_joined
      ((C.seamTransition (letters 0).1 (letters 0).2).trans initial)
    exact result.trans (congrArg initial (joined 0))

def boundedWordPlacement {N : ℕ} (initial : Plane ≃ᵃⁱ[ℝ] Plane) (word : C.BoundedSeamWord N) :
    Plane ≃ᵃⁱ[ℝ] Plane := C.wordPlacement (List.ofFn word.2) initial

theorem finite_boundedWordPlacements (N : ℕ) (initial : Plane ≃ᵃⁱ[ℝ] Plane) :
    (Set.range (C.boundedWordPlacement (N := N) initial)).Finite :=
  Set.finite_range _

def PointSeamRoute.code {retain : Set C.Seam} {x : C.Realization retain}
    {a b : C.PointFiber retain x} (R : C.PointSeamRoute retain x a b)
    {N : ℕ} (bound : R.steps < N) : C.BoundedSeamWord N :=
  ⟨⟨R.steps, bound⟩, fun i => (R.seam i, R.side i)⟩

theorem PointSeamRoute.code_agrees {retain : Set C.Seam} {x : C.Realization retain}
    {a b : C.PointFiber retain x} (R : C.PointSeamRoute retain x a b)
    {N : ℕ} (bound : R.steps < N) (initial : Plane ≃ᵃⁱ[ℝ] Plane) :
    C.boundedWordPlacement initial (R.code C bound) b.val.2.val = initial a.val.2.val := by
  have joined (i : Fin R.steps) :
      C.seamTransition (R.seam i) (R.side i) (R.copy i.succ).val.2.val =
        (R.copy i.castSucc).val.2.val := by
    obtain ⟨q, first, last⟩ := R.crossing i
    rw [first, last]
    exact C.seamTransition_joined (R.seam i) (R.side i) q
  have result := C.wordPlacement_on_chain (fun i => (R.seam i, R.side i))
    (fun i => (R.copy i).val.2.val) joined initial
  rw [R.start, R.finish] at result
  exact result

end Unfoldings.TriangleComplex
