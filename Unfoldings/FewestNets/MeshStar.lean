module

public import Unfoldings.FewestNets.CheckedSpace

/-! Exact radial site stars in the subdivided icosahedral mesh. -/

@[expose] public section

namespace Unfoldings.FewestNets

open NormedSpace

/-- Unnormalized site coordinates and neighbors, in their cyclic order. -/
structure MeshStar (degree : ℕ) where
  site : Space
  neighbor : Fin degree → Space

namespace MeshStar

noncomputable section

/-- Height squared of an icosahedron face plane in unit-circumsphere coordinates. -/
def faceHeightSq : ℝ := (5 + 2 * Real.sqrt 5) / 15

def faceHeight : ℝ := Real.sqrt faceHeightSq

def faceScale : ℝ := Real.sqrt ((1 - faceHeightSq) / 4)

def cornerA : Space := WithLp.toLp 2 ![-(Real.sqrt 3 * faceScale), -faceScale, faceHeight]

def cornerB : Space := WithLp.toLp 2 ![Real.sqrt 3 * faceScale, -faceScale, faceHeight]

def cornerC : Space := WithLp.toLp 2 ![0, 2 * faceScale, faceHeight]

def stepU (q : ℕ) : Space := (q : ℝ)⁻¹ • (cornerB - cornerA)

def stepV (q : ℕ) : Space := (q : ℝ)⁻¹ • (cornerC - cornerA)

/-- The six neighbors of a site interior to one macroface. -/
def faceOffset (q : ℕ) (k : Fin 6) : Space :=
  let u := stepU q
  let v := stepV q
  ![u, v, v - u, (-1 : ℝ) • u, (-1 : ℝ) • v, u - v] k

/-- A face key orders the barycentric weights at C, B and A as q-i-j, i and j. -/
def face (q i j : ℕ) : MeshStar 6 :=
  let z := cornerC + ((i : ℝ) / q) • (cornerB - cornerC) +
    ((j : ℝ) / q) • (cornerA - cornerC)
  ⟨z, fun k => z + faceOffset q k⟩

/-- Reflection across the plane through the origin and the shared macroedge. -/
def reflectAB (x : Space) : Space :=
  let r := normalize (spatialCross cornerA cornerB)
  x - (2 * inner ℝ x r) • r

def seamNeighbor (q : ℕ) (z : Space) (k : Fin 6) : Space :=
  let u := stepU q
  let v := stepV q
  ![z + u, z + v, z + (v - u), z - u, reflectAB (z + (v - u)), reflectAB (z + v)] k

/-- The two off-face neighbors are the reflections across the shared macroedge. -/
def seam (q i : ℕ) : MeshStar 6 :=
  let z := cornerA + (i : ℝ) • stepU q
  ⟨z, seamNeighbor q z⟩

/-- The positive one-fifth turn about the macrovertex A, in Rodrigues form. -/
def fifthTurn (x : Space) : Space :=
  let r := normalize cornerA
  let c := (Real.sqrt 5 - 1) / 4
  let s := Real.sqrt (1 - c ^ 2)
  c • x + s • spatialCross r x + ((1 - c) * inner ℝ r x) • r

/-- The five neighbors at an original icosahedron vertex are a rotation orbit. -/
def pentagon (q : ℕ) : MeshStar 5 :=
  ⟨cornerA, fun k => fifthTurn^[k.val] (cornerA + stepU q)⟩

variable {n : ℕ} (star : MeshStar (n + 1))

def direction : Space := normalize star.site

def neighborDirection (i : Fin (n + 1)) : Space := normalize (star.neighbor i)

/-- The outward direction perpendicular to two successive chord edges. -/
def dual (i : Fin (n + 1)) : Space :=
  spatialCross (star.neighborDirection i - star.direction)
    (star.neighborDirection (i + 1) - star.direction)

def dualDirection (i : Fin (n + 1)) : Space := normalize (star.dual i)

/-- The unscaled gnomonic vertex, in the tangent plane at the site. -/
def gnomonicVertex (i : Fin (n + 1)) : Space :=
  (inner ℝ star.direction (star.dual i))⁻¹ • star.dual i - star.direction

end

end MeshStar
end Unfoldings.FewestNets
