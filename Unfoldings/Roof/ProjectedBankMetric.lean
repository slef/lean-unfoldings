module

public import Unfoldings.Roof.AngleBalance
public import Unfoldings.Complex.AffineProjectionChains
public import Unfoldings.Development.AffineProjection
public import Unfoldings.Development.AdditionalCuts
public import Unfoldings.Geometry.ChainConstruction
public import Unfoldings.Complex.BoundaryChainIntervalHeading

/-! Exact real phase and speed factors for original roof bank rolls and projected metric rolls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- The same original roof faces and seams, with their actual projected Euclidean metric. -/
def projectedMetricComplex : TriangleComplex.{u, v} Face :=
  C.affineProjectionComplex K.projectFaceEquiv K.projectedTriangle_joined

def projectedMetricChain {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) :
    (K.projectedMetricComplex.boundarySystem retain).Chain n :=
  C.affineProjectionChain K.projectFaceEquiv K.projectedTriangle_joined chain

/-- Identity placement of projected triangles retains opposite-side hinges after any cuts. -/
def projectedMetricDevelopment (retain : Set C.Seam) :
    FacewiseDevelopment K.projectedMetricComplex retain :=
  (C.affineProjectionDevelopment K.projectFaceEquiv K.projectedTriangle_joined
    (fun _ _ different => K.projectedTriangles_nonoverlapping different)).cut
      (Set.subset_univ retain)

def projectedMetricHeading {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) : Fin (n + 1) → ℝ :=
  K.projectedMetricComplex.boundaryChainRollHeading (K.projectedMetricChain chain)

theorem projectedMetricHeading_eq {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    K.projectedMetricHeading chain i = Fin.partialSum (fun j : Fin n =>
      Real.pi - K.projectedTotalAngle retain (C.boundaryEndVertex retain (chain.point j.succ))) i :=
  C.affineProjectionChain_heading K.projectFaceEquiv K.projectedTriangle_joined chain i

/-- A real, unreduced phase error on the actual same directed original bank. -/
def projectedMetricHeadingError {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) : ℝ :=
  C.boundaryChainRollHeading chain i - K.projectedMetricHeading chain i

/-- Intrinsic bank speed divided by the speed of its identical projected bank. -/
def projectedMetricStretch {retain : Set C.Seam} (p : C.BoundaryEnd retain) : ℝ :=
  C.boundaryBankLength p / K.projectedMetricComplex.boundaryBankLength
    (C.affineProjectionBoundaryEndEquiv K.projectFaceEquiv K.projectedTriangle_joined retain p)

theorem face_projection_upper (f : Face) (x y : Plane) :
    dist (K.projectFace f x) (K.projectFace f y) ≤ dist x y := by
  calc
    _ = ‖Cap.horizontal (K.folding.place f x - K.folding.place f y)‖ := by
      rw [map_sub, dist_eq_norm]
      rfl
    _ ≤ ‖K.folding.place f x - K.folding.place f y‖ := Cap.horizontal_norm_le _
    _ = dist x y := by rw [← dist_eq_norm, (K.folding.place f).isometry.dist_eq]

theorem projectedMetric_bank_length {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    let projected := K.projectedMetricComplex.boundaryBankLength
      (C.affineProjectionBoundaryEndEquiv K.projectFaceEquiv K.projectedTriangle_joined retain p)
    projected ≤ C.boundaryBankLength p ∧
      K.normal p.val.1.1 2 * C.boundaryBankLength p ≤ projected :=
  ⟨K.face_projection_upper p.val.1.1 _ _, K.face_projection_lower p.val.1.1 _ _⟩

/-- Actual projected speeds give the original reciprocal-normal stretch bound. -/
theorem projectedMetricStretch_bounds {c : ℝ} (positive : 0 < c)
    (height : ∀ f, c ≤ K.normal f 2) {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    1 ≤ K.projectedMetricStretch p ∧ K.projectedMetricStretch p ≤ c⁻¹ := by
  let q := C.affineProjectionBoundaryEndEquiv K.projectFaceEquiv K.projectedTriangle_joined retain p
  let a := C.boundaryBankLength p
  let b := K.projectedMetricComplex.boundaryBankLength q
  have bounds := K.projectedMetric_bank_length p
  have length_positive : 0 < b := K.projectedMetricComplex.boundaryBankLength_pos q
  change 1 ≤ a / b ∧ a / b ≤ c⁻¹
  constructor
  · exact (one_le_div₀ length_positive).mpr bounds.1
  · apply (div_le_iff₀ length_positive).mpr
    have lower : c * a ≤ b :=
      (mul_le_mul_of_nonneg_right (height _) (C.boundaryBankLength_pos p).le).trans bounds.2
    calc
      _ = c⁻¹ * (c * a) := by rw [← mul_assoc, inv_mul_cancel₀ positive.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left lower (inv_nonneg.mpr positive.le)

/-- The original rolled edge has its exact actual projected speed and unreduced phase factors. -/
theorem projectedMetric_bank_edge_factor {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (i : Fin (n + 1)) :
    (C.boundaryChainRoll chain).edge i =
      (K.projectedMetricStretch (chain.point i) : ℂ) *
        polarRay (K.projectedMetricHeadingError chain i) *
          (K.projectedMetricComplex.boundaryChainRoll (K.projectedMetricChain chain)).edge i := by
  let a := C.boundaryBankLength (chain.point i)
  let b := K.projectedMetricComplex.boundaryBankLength ((K.projectedMetricChain chain).point i)
  let α := C.boundaryChainRollHeading chain i
  let β := K.projectedMetricHeading chain i
  have intrinsic : (C.boundaryChainRoll chain).edge i = (a : ℂ) * polarRay α :=
    PolygonalChain.ofHeadings_edge _ _ _ i
  have projected : (K.projectedMetricComplex.boundaryChainRoll
      (K.projectedMetricChain chain)).edge i = (b : ℂ) * polarRay β :=
    PolygonalChain.ofHeadings_edge _ _ _ i
  change (C.boundaryChainRoll chain).edge i =
    ((a / b : ℝ) : ℂ) * polarRay (α - β) *
      (K.projectedMetricComplex.boundaryChainRoll (K.projectedMetricChain chain)).edge i
  rw [intrinsic, projected]
  have nonzero : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (K.projectedMetricComplex.boundaryBankLength_pos ((K.projectedMetricChain chain).point i)).ne'
  have phase : polarRay (α - β) * polarRay β = polarRay α := by
    rw [← polarRay_add, sub_add_cancel]
  rw [Complex.ofReal_div]
  calc
    _ = ((a : ℂ) / (b : ℂ)) * (b : ℂ) * polarRay α := by rw [div_mul_cancel₀ _ nonzero]
    _ = _ := by rw [← phase]; ring

/-- A projected interval keeps the exact difference of original unreduced heading prefixes. -/
theorem projectedMetricHeading_interval {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin (length + 1)) :
    K.projectedMetricHeading (chain.interval first length fits) i =
      K.projectedMetricHeading chain ⟨first + i.val, by omega⟩ -
        K.projectedMetricHeading chain ⟨first, by omega⟩ :=
  K.projectedMetricComplex.boundaryChainRollHeading_interval (K.projectedMetricChain chain)
    first length fits i

/-- The local actual phase error is precisely the difference of its global real error prefixes. -/
theorem projectedMetricHeadingError_interval {retain : Set C.Seam} {n : ℕ}
    (chain : (C.boundarySystem retain).Chain n) (first length : ℕ) (fits : first + length ≤ n)
    (i : Fin (length + 1)) :
    K.projectedMetricHeadingError (chain.interval first length fits) i =
      K.projectedMetricHeadingError chain ⟨first + i.val, by omega⟩ -
        K.projectedMetricHeadingError chain ⟨first, by omega⟩ := by
  dsimp only [projectedMetricHeadingError]
  rw [C.boundaryChainRollHeading_interval, K.projectedMetricHeading_interval]
  have index (j : Fin (length + 1)) :
      chain.intervalIndex first length fits j = ⟨first + j.val, by omega⟩ := rfl
  simp only [index, Fin.val_zero, Nat.add_zero]
  ring

end Unfoldings.ConvexRoof
